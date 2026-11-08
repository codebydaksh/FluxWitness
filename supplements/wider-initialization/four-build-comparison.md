# Cosine initialization across four local builds

All four builds used the frozen RC2 source on the same WSL host. The recorded checker certified both initialization thresholds in each case. The checks cover the initial arrays exported by --dump-u0. Cell indices start at zero.

| Runtime | Build | Certified maximum upper bound (approx.) | RC2 margin (approx.) | Dump SHA-256 |
|---|---|---:|---:|---|
| glibc | -O0 | 2.485378074949e-16 | 2.192505078e-21 | d85763c9d8c12f0d6b0a3941984934b59228f0075416cb1df0eda70dac135e98 |
| glibc | -O2 | 2.485378074949e-16 | 2.192505078e-21 | d85763c9d8c12f0d6b0a3941984934b59228f0075416cb1df0eda70dac135e98 |
| musl | -O0 | 2.485378074949e-16 | 2.192505078e-21 | ea312076ac9b85d31e0747f107e77f77ebcc46b582ea4031f416609d43c5a51d |
| musl | -O2 | 2.485378074949e-16 | 2.192505078e-21 | ea312076ac9b85d31e0747f107e77f77ebcc46b582ea4031f416609d43c5a51d |

The maximum upper bound occurred at cell 238 in all four builds. Each library produced identical binary64 values at both optimization levels. The rows below compare musl with glibc.

| Cell | glibc (hex) | musl (hex) | Signed distance in binary64 values |
|---:|---|---|---:|
| 66 | 0x1.6eef57bc66e6bp+0 | 0x1.6eef57bc66e6cp+0 | +1 |
| 68 | 0x1.6deb12fcc06cdp+0 | 0x1.6deb12fcc06cep+0 | +1 |
| 122 | 0x1.4930590eb64a5p+0 | 0x1.4930590eb64a6p+0 | +1 |
| 305 | 0x1.43551daa11677p-1 | 0x1.43551daa11678p-1 | +1 |
| 317 | 0x1.33e2cb2b9ef23p-1 | 0x1.33e2cb2b9ef24p-1 | +1 |

Evidence directories: wide-init-builds-a5rkyc7e and wide-init-musl-ypqdvwzx. Each result.json contains its exact rational certificate. The musl interpreter SHA-256 is dd2bad010bb70a62612bc5ecf63d9ab7c0edb65ddcc931d583e5981a1424298a.
