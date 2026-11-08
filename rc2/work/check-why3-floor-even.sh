#!/usr/bin/env bash
set -euo pipefail
work=$(cd "$(dirname "$0")" && pwd)
out="$work/../evidence"
run=$(mktemp -d "$out/why3-floor-even-XXXXXXXX")
echo "Evidence: $run"
exec > >(tee "$run/check.log") 2>&1
trap 'rc=$?; echo "$rc" > "$run/exit-code.txt"; if ((rc)); then echo "Stopped, exit $rc"; fi' EXIT
archive_hash=b7d112edd5bcce6bcce0023d2bc834eb2ae1a1c42d7aea44ffa124d649b50bea
archive="$HOME/.opam/download-cache/sha256/b7/$archive_hash"
theory_hash=57a096bcb20309ab323405fabfeb67699037289dc0223368526adab32fa9d6a7
wp="$out/c2-wp-postcondition-export-20261107/run-mUCtyS/model-ieee_float.mlw"
lean="$out/c2-rounding-construction-20261107-121623/C2RoundingConstruction.lean"
printf '%s  %s\n' "$archive_hash" "$archive" "$theory_hash" "$wp" \
    409af5d8441d9328b12f295cf056ca63183be906da54ff26858e8f2762a8cf92 "$lean" | sha256sum -c -
for tool in coqc coq_makefile coqchk make; do command -v "$tool" || exit 2; done
coqc --version
dpkg-query -W coq libcoq-flocq || true
if pgrep -x 'lean|cbmc|frama-c|alt-ergo|coqc|coqchk' >/dev/null; then echo "Proof process active"; exit 2; fi
cd "$run"
tar -xzf "$archive" why3-1.8.2/lib/coq why3-1.8.2/stdlib/ieee_float.mlw
cmp why3-1.8.2/stdlib/ieee_float.mlw "$wp"
cd why3-1.8.2/lib/coq
cp "$work/Why3FloorEven.v" .
sha256sum Why3FloorEven.v ieee_float/{Float64,GenericFloat,RoundingMode}.v
find . -name '*.v' | sort > source-list.txt
mapfile -t sources < source-list.txt
export OCAMLRUNPARAM=d=1
ulimit -v 3145728
printf 'OCAMLRUNPARAM=%s; virtual address limit (KiB): %s\n' "$OCAMLRUNPARAM" "$(ulimit -v)"
coqc --version
coq_makefile -R . Why3 "${sources[@]}" -o Makefile.bridge
if [[ ${1:-} == --reuse-deps ]]; then
    cache="$out/why3-floor-even-cS6zwtvb/why3-1.8.2/lib/coq"
    printf '%s  %s\n' 88152babdd6cb3bff5a5ad2d964ed044f606f7c8c2aa053d0b0557a72e013236 "$cache/ieee_float/Float64.vo" | sha256sum -c -
    while IFS= read -r obj; do
        rel=${obj#"$cache/"}
        [[ $rel != Why3FloorEven.vo ]] || continue
        cmp "$cache/${rel%.vo}.v" "${rel%.vo}.v"
        cp "$obj" "$rel"
        sha256sum "$rel" >> "$run/reused-objects.sha256"
    done < <(find "$cache" -type f -name '*.vo' | sort)
fi
timeout 900s make -j1 -f Makefile.bridge Why3FloorEven.vo
timeout 600s coqchk -silent -R . Why3 Why3.Why3FloorEven
sha256sum Why3FloorEven.vo
echo 'KERNEL_CHECKED; review Print Assumptions in check.log'
