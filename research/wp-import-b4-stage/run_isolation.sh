#!/usr/bin/env bash
# Diagnostic only: isolate original WP stage goals without changing probe source.
set -euo pipefail
export PATH="/usr/local/bin:$PATH"

mkdir -p /results
frama-c -version | tee /results/frama-version.txt
alt-ergo --version | tee /results/alt-ergo-version.txt
test "$(alt-ergo --version)" = "v2.6.4"
why3 config detect | tee /results/why3-detect.txt

COMMON=(
  -machdep x86_64 -wp -wp-fct compare_update
  -wp-model Typed+float -wp-rte -wp-prover qed,alt-ergo
  -wp-par 1 -wp-timeout 60 -wp-print
)

# Previous unmodified B002-B4 source: all three assertions were valid in 20/22.
echo "CONTROL: previous B002-B4 combined stage goals"
set +e
timeout 190s frama-c "${COMMON[@]}" \
  -wp-prop stage_left,stage_center,stage_right \
  -wp-out /results/baseline-vcs \
  /source/research/wp-import-b4/probe_b002b4.c \
  > /results/baseline.log 2>&1
control_rc=$?
set -e
echo "$control_rc" > /results/baseline.exit
echo "BASELINE_EXIT=$control_rc"

# Candidate source is IDENTICAL to previous verified stencil-cut source.
# Goal selection controls only proof scheduling; no ACSL proof assumptions added.
for goal in stage_left stage_center stage_right; do
  echo "ISOLATED_STAGE=$goal"
  set +e
  timeout 100s frama-c "${COMMON[@]}" \
    -wp-prop "$goal" \
    -wp-out "/results/$goal-vcs" \
    /source/research/wp-import-b4-cut/probe_b002b4_cut.c \
    > "/results/$goal.log" 2>&1
  rc=$?
  set -e
  echo "$rc" > "/results/$goal.exit"
  echo "STAGE_EXIT_$goal=$rc"
done

for goal in baseline stage_left stage_center stage_right; do
  if test -d "/results/$goal-vcs"; then
    find "/results/$goal-vcs" -type f | sort | sed "s@/results/@@g" > "/results/$goal-files.txt"
  fi
done

# A host runner cannot traverse the image user's private WP generated folders.
# Preserve their exact bytes in a readable archive; do not change or remove VCs.
tar -czf /results/generated-vcs.tgz -C /results \
  baseline-vcs stage_left-vcs stage_center-vcs stage_right-vcs
chmod 644 /results/generated-vcs.tgz
chmod -R a+rX /results

