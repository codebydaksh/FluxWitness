#define HEAT_NO_MAIN 1
/* heat_1d_v2.c
 *
 * Refactor of heat_1d.c for verification. Changes vs the original, and nothing else:
 *   1. heat_step takes caller-supplied scratch buffers: no malloc inside the kernel,
 *      so memory safety of the loop is a property of one allocation in main.
 *   2. dx*dx is computed once per step (same operation, same operands: bitwise identical value).
 *   3. heat_step rejects CFL violations: D*dt > 0.45*dx^2 (the 0.45 leaves margin for the
 *      rounding in this test, so the real-number premise r <= 1/2 follows when it passes).
 *   4. Driver uses an integer step count N and dt = T/N: no floating clock, no partial step.
 *   5. Output uses %.17g (round-trips exactly); --dump-u0 prints the initial array as %a.
 *
 * The floating-point expression tree of compute_L and the two Heun stages is UNCHANGED, so
 * heat_step_rounding_v2.g applies to it.
 *
 * Build (no FMA contraction, strict FP):
 *   gcc   -std=c11 -O0 -ffp-contract=off -o heat_v2 heat_1d_v2.c -lm
 *   cl    /std:c11 /O2 /fp:strict heat_1d_v2.c          (x64, do NOT add /arch:AVX2)
 * Cosine initial data (same as the experiment harness): add -DIC_COSINE
 * Other grid sizes: -DNX=800
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#ifndef NX
#define NX 400
#endif
#define D_DIFF  0.01
#define X_LEFT  (-3.0)
#define X_RIGHT 3.0
#define SIGMA0  0.30
#define X0      0.0
#define T_END   1.0

/* Functional target, independent of the C loop body.
   ACSL arithmetic is over mathematical reals; each round_double denotes ONE
   binary64 nearest-even operation. Inputs are the exact real values of
   stored binary64 values. 0.01 is rounded once as a C double literal.
   Not a proof of absence of NaN/Inf, FMA behavior, or compiled assembly. */
/*@
  logic double fw_compute_cell(real l, real c, real r, real q) =
    \round_double(\NearestEven,
      \round_double(\NearestEven, 0.01) *
      \round_double(\NearestEven,
        \round_double(\NearestEven,
          \round_double(\NearestEven,
            r - \round_double(\NearestEven, 2.0 * c)) + l) / q));
*/

/* Scalar arithmetic lemma. The premises are exactly the facts WP already has at the store:
   finite inputs in the stated ranges and finite results of each of the five operations. */
/*@
  lemma fw_cell_scalar:
    \forall double l, c, r, q;
      \is_finite(l) && \is_finite(c) && \is_finite(r) && \is_finite(q) &&
      -4.0 <= l <= 4.0 && -4.0 <= c <= 4.0 && -4.0 <= r <= 4.0 &&
      0.0001 <= q <= 1.0 &&
      \is_finite(\mul_double((double)2.0, c)) &&
      \is_finite(\sub_double(r, \mul_double((double)2.0, c))) &&
      \is_finite(\add_double(\sub_double(r, \mul_double((double)2.0, c)), l)) &&
      \is_finite(\div_double(\add_double(\sub_double(r, \mul_double((double)2.0, c)), l), q)) &&
      \is_finite(\mul_double((double)0.01,
        \div_double(\add_double(\sub_double(r, \mul_double((double)2.0, c)), l), q))) ==>
      \mul_double((double)0.01,
        \div_double(\add_double(\sub_double(r, \mul_double((double)2.0, c)), l), q))
      == fw_compute_cell(l, c, r, q);
*/

/*@
  requires 1 <= n && n <= 400;
  requires \valid_read(u + (0 .. n-1));
  requires \valid(L + (0 .. n-1));
  requires \separated(u + (0 .. n-1), L + (0 .. n-1));
  requires \is_finite(dx2);
  requires \forall integer k; 0 <= k < n ==> \is_finite(u[k]);
  requires 0.0001 <= dx2 <= 1.0;
  requires \forall integer k; 0 <= k < n ==> -4.0 <= u[k] <= 4.0;
  assigns L[0 .. n-1];
  ensures \forall integer j; 0 <= j < n ==> \is_finite(L[j]) && -1601.0 <= L[j] <= 1601.0;
  ensures (dx2 >= 0.0002 && (\forall integer k; 0 <= k < n ==> -2.0 <= u[k] <= 2.0)) ==>
    (\forall integer j; 0 <= j < n ==> -401.0 <= L[j] <= 401.0);
  ensures \forall integer k; 0 <= k < n ==> u[k] == \old(u[k]);
  ensures \forall integer k; 0 <= k < n ==>
    L[k] == fw_compute_cell(
      \old(u[k == 0 ? 0 : k-1]), \old(u[k]),
      \old(u[k == n-1 ? n-1 : k+1]), dx2);
*/
static void compute_L(const double *u, double *L, int n, double dx2) {
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \is_finite(dx2);
      loop invariant \forall integer k; 0 <= k < n ==> \is_finite(u[k]);
      loop invariant 0.0001 <= dx2 <= 1.0;
      loop invariant \forall integer k; 0 <= k < n ==> -4.0 <= u[k] <= 4.0;
      loop invariant \forall integer k; 0 <= k < i ==>
        L[k] == fw_compute_cell(
          u[k == 0 ? 0 : k-1], u[k],
          u[k == n-1 ? n-1 : k+1], dx2);
      loop invariant \forall integer j; 0 <= j < i ==> \is_finite(L[j]) && -1601.0 <= L[j] <= 1601.0;
      loop invariant (dx2 >= 0.0002 && (\forall integer k; 0 <= k < n ==> -2.0 <= u[k] <= 2.0)) ==>
        (\forall integer j; 0 <= j < i ==> -401.0 <= L[j] <= 401.0);
      loop assigns i, L[0 .. n-1];
      loop variant n-i;
    */
    for (int i = 0; i < n; i++) {
        int im1 = (i == 0)     ? 0     : i - 1;
        int ip1 = (i == n - 1) ? n - 1 : i + 1;
        /*@ assert fw_cell_inputs:
          \is_finite(u[im1]) && \is_finite(u[i]) && \is_finite(u[ip1]) && \is_finite(dx2) &&
          -4.0 <= u[im1] <= 4.0 && -4.0 <= u[i] <= 4.0 && -4.0 <= u[ip1] <= 4.0 &&
          0.0001 <= dx2 <= 1.0; */
        double uxx = (u[ip1] - 2.0 * u[i] + u[im1]) / dx2;
        L[i] = D_DIFF * uxx;
        /*@ assert fw_cell_equation: L[i] == fw_compute_cell(u[im1], u[i], u[ip1], dx2); */
        /*@ assert fw_earlier_cells: \forall integer j; 0 <= j < i ==>
              L[j] == fw_compute_cell(u[j == 0 ? 0 : j-1], u[j],
                                      u[j == n-1 ? n-1 : j+1], dx2); */
        /*@ assert fw_current_clamped: L[i] ==
              fw_compute_cell(u[i == 0 ? 0 : i-1], u[i],
                              u[i == n-1 ? n-1 : i+1], dx2); */
    }
}

/* One SSP-RK2 (Heun) step in place on u[0..n-1].
 * Precondition (C level): u, L, U1 each point to n valid writable doubles, pairwise disjoint.
 * Returns -1 without modifying u if arguments are invalid or CFL/range guards fail. */
/*@
 logic integer heat_left(integer j) = j > 0 ? j-1 : 0;
 logic integer heat_right(integer j, integer n) = j < n-1 ? j+1 : n-1;
 logic double heat_euler_fp(double l, double c, double r, double dt, double q) =
   (double)(c + (double)(dt * fw_compute_cell(l,c,r,q)));
 logic double heat_stage_fp{S}(double *u, integer j, integer n, double dt, double q) =
   heat_euler_fp(\at(u[heat_left(j)],S), \at(u[j],S),
                 \at(u[heat_right(j,n)],S), dt, q);
 logic double heat_heun_fp{S}(double *u, integer j, integer n, double dt, double q) =
   (double)((double)(0.5 * \at(u[j],S)) +
     (double)(0.5 * heat_euler_fp(heat_stage_fp{S}(u,heat_left(j),n,dt,q),
       heat_stage_fp{S}(u,j,n,dt,q), heat_stage_fp{S}(u,heat_right(j,n),n,dt,q),dt,q)));
*/

/*@
 requires n == 400;
 requires \is_finite(dx) && dx == (double)(3.0/200.0);
 requires \is_finite(dt) && 0.0 <= dt <= 0.0045;
 requires \valid(u + (0..n-1));
 requires \valid(L + (0..n-1));
 requires \valid(U1 + (0..n-1));
 requires \separated(u + (0..n-1), L + (0..n-1), U1 + (0..n-1));
 requires \forall integer j; 0 <= j < n ==> \is_finite(u[j]) && -2.0 <= u[j] <= 2.0;
 assigns u[0..n-1], L[0..n-1], U1[0..n-1];
 ensures \result == 0;
 ensures \result == 0 ==> \forall integer j; 0 <= j < n ==>
   u[j] == heat_heun_fp{Pre}(u,j,n,dt,(double)(dx*dx));
 ensures \result == 0 ==> \forall integer j; 0 <= j < n ==> \is_finite(u[j]);
*/
static int heat_step(double *u, double *L, double *U1, int n, double dx, double dt) {
    if (u == NULL || L == NULL || U1 == NULL || n <= 0 ||
        !isfinite(dx) || dx <= 0 || !isfinite(dt) || dt < 0) return -1;
    const double dx2 = dx * dx;
    if (!isfinite(dx2) || dx2 < 1e-100) return -1;
    /*@ assert stored_denominator: dx2 == (double)(4150517416584649.0/18446744073709551616.0); */
    if (dt * D_DIFF > 0.45 * dx2) return -1;

    compute_L(u, L, n, dx2);
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==>
        U1[j] == heat_stage_fp{Pre}(u,j,n,dt,(double)(dx*dx));
      loop invariant \forall integer j; 0 <= j < i ==>
        \is_finite(U1[j]) && -4.0 <= U1[j] <= 4.0;
      loop assigns i, U1[0..n-1];
      loop variant n-i;
    */
    for (int i = 0; i < n; i++) U1[i] = u[i] + dt * L[i];
    /*@ assert stage_completed:
          \forall integer j; 0 <= j < n ==>
            U1[j] == heat_stage_fp{Pre}(u,j,n,dt,(double)(dx*dx)) &&
            \is_finite(U1[j]) && -4.0 <= U1[j] <= 4.0; */

    compute_L(U1, L, n, dx2);
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==>
        u[j] == heat_heun_fp{Pre}(u,j,n,dt,(double)(dx*dx)) &&
        \is_finite(u[j]);
      loop invariant \forall integer j; i <= j < n ==> u[j] == \at(u[j],Pre);
      loop invariant \forall integer j; i <= j < n ==>
        \is_finite(u[j]) && -2.0 <= u[j] <= 2.0;
      loop assigns i, u[0..n-1];
      loop variant n-i;
    */
    for (int i = 0; i < n; i++) {
        /*@ assert input_bounds: \is_finite(U1[i]) && -4.0 <= U1[i] <= 4.0 &&
              \is_finite(L[i]) && -1601.0 <= L[i] <= 1601.0 &&
              \is_finite(u[i]) && -2.0 <= u[i] <= 2.0; */
        /*@ assert final_stage_left:
              U1[heat_left(i)] ==
              heat_stage_fp{Pre}(u, heat_left(i), n, dt, (double)(dx*dx)); */
        /*@ assert final_stage_center:
              U1[i] ==
              heat_stage_fp{Pre}(u, i, n, dt, (double)(dx*dx)); */
        /*@ assert final_stage_right:
              U1[heat_right(i,n)] ==
              heat_stage_fp{Pre}(u, heat_right(i,n), n, dt, (double)(dx*dx)); */
        /*@ assert final_second_stencil_equation:
              L[i] ==
              fw_compute_cell(U1[heat_left(i)], U1[i],
                         U1[heat_right(i,n)], dx2); */
        double tmp = U1[i] + dt * L[i];
        /*@ assert final_second_euler_equation:
              tmp == heat_euler_fp(U1[heat_left(i)], U1[i],
                                   U1[heat_right(i,n)], dt, dx2); */
        /*@ assert final_second_stage_reference_equation:
              tmp == heat_euler_fp(
                heat_stage_fp{Pre}(u, heat_left(i), n, dt, (double)(dx*dx)),
                heat_stage_fp{Pre}(u, i, n, dt, (double)(dx*dx)),
                heat_stage_fp{Pre}(u, heat_right(i,n), n, dt, (double)(dx*dx)),
                dt, (double)(dx*dx)); */

        /*@ assert final_tmp_bounds: \is_finite(tmp) && -12.0 <= tmp <= 12.0; */
        u[i] = 0.5 * u[i] + 0.5 * tmp;
        /*@ assert final_reference_equation: u[i] ==
              heat_heun_fp{Pre}(u,i,n,dt,(double)(dx*dx)); */
    }
    /*@ assert final_completed:
          \forall integer j; 0 <= j < n ==>
            u[j] == heat_heun_fp{Pre}(u,j,n,dt,(double)(dx*dx)) &&
            \is_finite(u[j]); */
    return 0;
}

#ifndef HEAT_NO_MAIN
int main(int argc, char **argv) {
    const double dx = (X_RIGHT - X_LEFT) / NX;
    double *buf = malloc(3 * (size_t)NX * sizeof(double));
    if (buf == NULL) { fputs("Allocation failed\n", stderr); return EXIT_FAILURE; }
    double *u = buf, *L = buf + NX, *U1 = buf + 2 * (size_t)NX;

    for (int i = 0; i < NX; i++) {
        double x = X_LEFT + (i + 0.5) * dx;
#ifdef IC_COSINE
        const double PI = 3.14159265358979323846;
        u[i] = 1.0 + 0.5 * cos(PI * (x + 3.0) / 6.0);
#else
        double dr = (x - X0) / SIGMA0;
        u[i] = exp(-0.5 * dr * dr);
#endif
    }

    if (argc > 1 && strcmp(argv[1], "--dump-u0") == 0) {
        for (int i = 0; i < NX; i++) printf("%a\n", u[i]);
        free(buf);
        return 0;
    }

    const double dt_max = 0.4 * dx * dx / (2.0 * D_DIFF);
    const int    N      = (int)ceil(T_END / dt_max);   /* integer step count */
    const double dt     = T_END / N;                    /* elapsed time = N*dt, dt a stored double */

    for (int k = 0; k < N; k++) {
        if (heat_step(u, L, U1, NX, dx, dt) != 0) {
            fputs("Heat step failed\n", stderr);
            free(buf);
            return EXIT_FAILURE;
        }
    }

    printf("x,u\n");
    for (int i = 0; i < NX; i++) {
        double x = X_LEFT + (i + 0.5) * dx;
        printf("%.17g,%.17g\n", x, u[i]);
    }
    free(buf);
    return 0;
}
#endif

/*@ logic real R(real x) = (real)\round_double(\NearestEven,x);
*/
/*@ requires \is_finite(l) && \is_finite(c) && \is_finite(r);
    requires -2.0 <= l <= 2.0 && -2.0 <= c <= 2.0 && -2.0 <= r <= 2.0;
    assigns \nothing;
    ensures first_range: -4.0 <=
      heat_euler_fp(l,c,r,(double)(5170051590165233.0/1152921504606846976.0),
        (double)(4150517416584649.0/18446744073709551616.0)) <= 4.0;
*/
void first_bound(double l,double c,double r) {
    double row[3] = {l,c,r}, rhs[3];
    const double q = 4150517416584649.0 / 18446744073709551616.0;
    const double dt = 5170051590165233.0 / 1152921504606846976.0;
    compute_L(row,rhs,3,q);
    /*@ assert stencil_range: -401.0 <= rhs[1] <= 401.0; */
    /*@ assert stencil_value: rhs[1] == fw_compute_cell(l,c,r,q); */
    double inc = dt * rhs[1];
    double value = c + inc;
    /*@ assert sum_range: -4.0 <= value <= 4.0; */
    /*@ assert sum_value: value == heat_euler_fp(l,c,r,dt,q); */
}

/*@ requires \is_finite(l) && \is_finite(c) && \is_finite(r);
    requires -4.0 <= l <= 4.0 && -4.0 <= c <= 4.0 && -4.0 <= r <= 4.0;
    assigns \nothing;
    ensures second_range: -12.0 <=
      heat_euler_fp(l,c,r,(double)(5170051590165233.0/1152921504606846976.0),
        (double)(4150517416584649.0/18446744073709551616.0)) <= 12.0;
*/
void second_bound(double l,double c,double r) {
    double row[3] = {l,c,r}, rhs[3];
    const double q = 4150517416584649.0 / 18446744073709551616.0;
    const double dt = 5170051590165233.0 / 1152921504606846976.0;
    compute_L(row,rhs,3,q);
    /*@ assert stencil_range: -1601.0 <= rhs[1] <= 1601.0; */
    /*@ assert stencil_value: rhs[1] == fw_compute_cell(l,c,r,q); */
    double inc = dt * rhs[1];
    double value = c + inc;
    /*@ assert sum_range: -12.0 <= value <= 12.0; */
    /*@ assert sum_value: value == heat_euler_fp(l,c,r,dt,q); */
}

/*@ logic double c5_average(double c,double t) =
      (double)((double)(0.5*c) + (double)(0.5*t)); */
/*@ requires \is_finite(c) && \is_finite(t) && -2.0 <= c <= 2.0 && -12.0 <= t <= 12.0;
    assigns \nothing;
    ensures decoded_average: (real)c5_average(c,t) ==
      R(R((1.0/2.0)*(real)c) + R((1.0/2.0)*(real)t));
    ensures finite_average: \is_finite(c5_average(c,t));
*/
void compare_average(double c,double t) {}
