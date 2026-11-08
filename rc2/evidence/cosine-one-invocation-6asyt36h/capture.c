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

static void compute_L(const double *u, double *L, int n, double dx2) {
    for (int i = 0; i < n; i++) {
        int im1 = (i == 0)     ? 0     : i - 1;
        int ip1 = (i == n - 1) ? n - 1 : i + 1;
        double uxx = (u[ip1] - 2.0 * u[i] + u[im1]) / dx2;
        L[i] = D_DIFF * uxx;
    }
}

/* One SSP-RK2 (Heun) step in place on u[0..n-1].
 * Precondition (C level): u, L, U1 each point to n valid writable doubles, pairwise disjoint.
 * Returns -1 without modifying u if arguments are invalid or CFL/range guards fail. */
static int heat_step(double *u, double *L, double *U1, int n, double dx, double dt) {
    if (u == NULL || L == NULL || U1 == NULL || n <= 0 ||
        !isfinite(dx) || dx <= 0 || !isfinite(dt) || dt < 0) return -1;
    const double dx2 = dx * dx;
    if (!isfinite(dx2) || dx2 < 1e-100) return -1;
    if (dt * D_DIFF > 0.45 * dx2) return -1;

    compute_L(u, L, n, dx2);
    for (int i = 0; i < n; i++) U1[i] = u[i] + dt * L[i];

    compute_L(U1, L, n, dx2);
    for (int i = 0; i < n; i++) {
        double tmp = U1[i] + dt * L[i];
        u[i] = 0.5 * u[i] + 0.5 * tmp;
    }
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

    double initial_copy[NX];
    memcpy(initial_copy, u, sizeof(initial_copy));
    for (int k = 0; k < N; k++) {
        if (heat_step(u, L, U1, NX, dx, dt) != 0) {
            fputs("Heat step failed\n", stderr);
            free(buf);
            return EXIT_FAILURE;
        }
    }

    for (int i = 0; i < NX; i++)
        if (fprintf(stderr, "%a\n", initial_copy[i]) < 0) return EXIT_FAILURE;
    if (fflush(stderr) != 0) return EXIT_FAILURE;
    printf("x,u\n");
    for (int i = 0; i < NX; i++) {
        double x = X_LEFT + (i + 0.5) * dx;
        printf("%.17g,%.17g\n", x, u[i]);
    }
    free(buf);
    return 0;
}
#endif
