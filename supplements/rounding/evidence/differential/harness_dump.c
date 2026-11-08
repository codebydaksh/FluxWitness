/* Differential-test harness. Includes the UNMODIFIED kernel; replicates only main()'s setup. */
#define HEAT_NO_MAIN
#include "heat_1d_v2.c"

static void dump(int k, const double *u) {
    printf("STEP %d\n", k);
    for (int i = 0; i < NX; i++) printf("%a\n", u[i]);
}

int main(void) {
    const double dx = (X_RIGHT - X_LEFT) / NX;
    double *buf = malloc(3 * (size_t)NX * sizeof(double));
    if (buf == NULL) return EXIT_FAILURE;
    double *u = buf, *L = buf + NX, *U1 = buf + 2 * (size_t)NX;
    for (int i = 0; i < NX; i++) {
        double x = X_LEFT + (i + 0.5) * dx;
        const double PI = 3.14159265358979323846;
        u[i] = 1.0 + 0.5 * cos(PI * (x + 3.0) / 6.0);
    }
    const double dt_max = 0.4 * dx * dx / (2.0 * D_DIFF);
    const int    N      = (int)ceil(T_END / dt_max);
    const double dt     = T_END / N;
    printf("PARAMS %a %a %d\n", dx, dt, N);
    for (int k = 0; k <= N; k++) {
        if (k == 0 || k == 10 || k == 50 || k == 100 || k == 150 || k == 200 || k == N) dump(k, u);
        if (k == N) break;
        if (heat_step(u, L, U1, NX, dx, dt) != 0) return EXIT_FAILURE;
    }
    free(buf);
    return 0;
}