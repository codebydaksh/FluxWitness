/*@ logic double fw_compute_cell(real l, real c, real r, real q) =
    \round_double(\NearestEven,
      \round_double(\NearestEven, 0.01) *
      \round_double(\NearestEven,
        \round_double(\NearestEven,
          \round_double(\NearestEven,
            r - \round_double(\NearestEven, 2.0 * c)) + l) / q));
*/
/*@ logic integer heat_left(integer j) = j > 0 ? j-1 : 0;
 logic integer heat_right(integer j, integer n) = j < n-1 ? j+1 : n-1;
 logic double heat_euler_fp(double l, double c, double r, double dt, double q) =
   (double)(c + (double)(dt * fw_compute_cell(l,c,r,q)));
*/
/*@ axiomatic DriverReference {
      logic double ref_cell(integer k, integer j);
    }
    logic double ref_stage(integer k, integer j, double dt, double q) =
      heat_euler_fp(ref_cell(k,heat_left(j)),ref_cell(k,j),
                    ref_cell(k,heat_right(j,400)),dt,q);
    logic double ref_update(integer k, integer j, double dt, double q) =
      (double)((double)(0.5 * ref_cell(k,j)) +
        (double)(0.5 * heat_euler_fp(ref_stage(k,heat_left(j),dt,q),
          ref_stage(k,j,dt,q),ref_stage(k,heat_right(j,400),dt,q),dt,q)));
*/
/*@ logic real R(real x) = (real)\round_double(\NearestEven,x);
    logic real c5_e(real l, real c, real r, real dt) =
      \let d = 5764607523034235.0 / 576460752303423488.0;
      \let q = 4150517416584649.0 / 18446744073709551616.0;
      \let stencil = R (d * R (R (R (r - R (2.0*c)) + l) / q));
      R (c + R (dt * stencil));
    logic integer c5_l(integer j) = j > 0 ? j-1 : 0;
    logic integer c5_r(integer j) = j < 399 ? j+1 : 399;
    logic real c5_u(integer k,integer j) = (real)ref_cell(k,j);
    logic real c5_s(integer k,integer j,real dt) =
      c5_e(c5_u(k,c5_l(j)),c5_u(k,j),c5_u(k,c5_r(j)),dt);
    logic real c5_update(integer k,integer j,real dt) =
      \let t = c5_e(c5_s(k,c5_l(j),dt),c5_s(k,j,dt),c5_s(k,c5_r(j),dt),dt);
      R(R((1.0/2.0)*c5_u(k,j)) + R((1.0/2.0)*t));
*/
/*@ logic double c5_average(double c,double t) =
      (double)((double)(0.5*c) + (double)(0.5*t)); */
/*@ lemma b002b1_decoded_euler:
    \forall double l,c,r; (\is_finite(l) && \is_finite(c) && \is_finite(r)) && (-4.0 <= l <= 4.0 && -4.0 <= c <= 4.0 && -4.0 <= r <= 4.0) ==> ((real)heat_euler_fp(l,c,r,(double)(5170051590165233.0/1152921504606846976.0),
        (double)(4150517416584649.0/18446744073709551616.0)) ==
      c5_e((real)l,(real)c,(real)r,5170051590165233.0/1152921504606846976.0));
*/
/*@ lemma b002b2_finite_euler:
    \forall double l,c,r; (\is_finite(l) && \is_finite(c) && \is_finite(r)) && (-4.0 <= l <= 4.0 && -4.0 <= c <= 4.0 && -4.0 <= r <= 4.0) ==> (\is_finite(heat_euler_fp(l,c,r,(double)(5170051590165233.0/1152921504606846976.0),
        (double)(4150517416584649.0/18446744073709551616.0))));
*/
/*@ requires imported_first_range: \forall double l,c,r; (\is_finite(l) && \is_finite(c) && \is_finite(r)) && (-2.0 <= l <= 2.0 && -2.0 <= c <= 2.0 && -2.0 <= r <= 2.0) ==> (-4.0 <=
      heat_euler_fp(l,c,r,(double)(5170051590165233.0/1152921504606846976.0),
        (double)(4150517416584649.0/18446744073709551616.0)) <= 4.0);
    requires imported_second_range: \forall double l,c,r; (\is_finite(l) && \is_finite(c) && \is_finite(r)) && (-4.0 <= l <= 4.0 && -4.0 <= c <= 4.0 && -4.0 <= r <= 4.0) ==> (-12.0 <=
      heat_euler_fp(l,c,r,(double)(5170051590165233.0/1152921504606846976.0),
        (double)(4150517416584649.0/18446744073709551616.0)) <= 12.0);
    requires imported_decoded_average: \forall double c,t; (\is_finite(c) && \is_finite(t) && -2.0 <= c <= 2.0 && -12.0 <= t <= 12.0) ==> ((real)c5_average(c,t) ==
      R(R((1.0/2.0)*(real)c) + R((1.0/2.0)*(real)t)));
    requires imported_finite_average: \forall double c,t; (\is_finite(c) && \is_finite(t) && -2.0 <= c <= 2.0 && -12.0 <= t <= 12.0) ==> (\is_finite(c5_average(c,t)));
    requires 0 <= k < 223 && 0 <= j < 400;
    requires \forall integer i; 0 <= i < 400 ==>
      \is_finite(ref_cell(k,i)) && -2.0 <= c5_u(k,i) <= 2.0;
    assigns \nothing;
    ensures decoded_update:
      (real)ref_update(k,j,(double)(1.0/223.0),
        (double)((double)(3.0/200.0)*(double)(3.0/200.0))) ==
      c5_update(k,j,5170051590165233.0/1152921504606846976.0);
    ensures finite_update:
      \is_finite(ref_update(k,j,(double)(1.0/223.0),
        (double)((double)(3.0/200.0)*(double)(3.0/200.0))));
*/
void compare_update(int k,int j) {
/*@ assert stage_left: \is_finite(ref_stage(k,heat_left(j),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0))) && -4.0 <= ref_stage(k,heat_left(j),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)) <= 4.0 && (real)ref_stage(k,heat_left(j),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)) == c5_s(k,heat_left(j),(5170051590165233.0/1152921504606846976.0)); */
/*@ assert stage_center: \is_finite(ref_stage(k,j,(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0))) && -4.0 <= ref_stage(k,j,(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)) <= 4.0 && (real)ref_stage(k,j,(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)) == c5_s(k,j,(5170051590165233.0/1152921504606846976.0)); */
/*@ assert stage_right: \is_finite(ref_stage(k,heat_right(j,400),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0))) && -4.0 <= ref_stage(k,heat_right(j,400),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)) <= 4.0 && (real)ref_stage(k,heat_right(j,400),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)) == c5_s(k,heat_right(j,400),(5170051590165233.0/1152921504606846976.0)); */
/*@ assert second_stage: \is_finite(heat_euler_fp(ref_stage(k,heat_left(j),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),ref_stage(k,j,(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),ref_stage(k,heat_right(j,400),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0))) && -12.0 <= heat_euler_fp(ref_stage(k,heat_left(j),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),ref_stage(k,j,(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),ref_stage(k,heat_right(j,400),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)) <= 12.0 && (real)heat_euler_fp(ref_stage(k,heat_left(j),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),ref_stage(k,j,(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),ref_stage(k,heat_right(j,400),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)) == c5_e(c5_s(k,heat_left(j),(5170051590165233.0/1152921504606846976.0)),c5_s(k,j,(5170051590165233.0/1152921504606846976.0)),c5_s(k,heat_right(j,400),(5170051590165233.0/1152921504606846976.0)),(5170051590165233.0/1152921504606846976.0)); */
/*@ assert combination: \is_finite(c5_average(ref_cell(k,j),heat_euler_fp(ref_stage(k,heat_left(j),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),ref_stage(k,j,(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),ref_stage(k,heat_right(j,400),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)))) && (real)c5_average(ref_cell(k,j),heat_euler_fp(ref_stage(k,heat_left(j),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),ref_stage(k,j,(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),ref_stage(k,heat_right(j,400),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0)),(double)(5170051590165233.0/1152921504606846976.0),(double)(4150517416584649.0/18446744073709551616.0))) == c5_update(k,j,(5170051590165233.0/1152921504606846976.0)); */
}
/*@ assigns \nothing;
    ensures reference_decode: \forall real x;
      -2.0 <= x <= 2.0 && R(x) == x ==>
        \is_finite((double)x) && (real)((double)x) == x;
*/
void compare_decode(void) {}
