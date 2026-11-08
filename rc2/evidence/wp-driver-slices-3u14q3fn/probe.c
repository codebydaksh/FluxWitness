#include <stdlib.h>
#define NX 400

/*@ requires backing: \valid(buf + (0 .. 1199));
    assigns \nothing;
*/
void driver_slices(double *buf) {
    double *u = buf, *L = buf + NX, *U1 = buf + 2 * (size_t)NX;
    /*@ assert driver_valid_u: \valid(u + (0 .. 399)); */
    /*@ assert driver_valid_L: \valid(L + (0 .. 399)); */
    /*@ assert driver_valid_U1: \valid(U1 + (0 .. 399)); */
    /*@ assert driver_disjoint:
          \separated(u + (0 .. 399), L + (0 .. 399), U1 + (0 .. 399)); */
}

void driver_allocate(void) {
    double *buf = malloc(3 * (size_t)NX * sizeof(double));
    if (buf == NULL) return;
    driver_slices(buf);
}
