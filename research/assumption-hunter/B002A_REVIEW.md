# Assumption Hunter B002-A — source-based WP premise audit

**Status:** Evidence audit completed; no new semantic bridge proved. Do not describe this document as closure of the C/WP-to-Lean boundary.

**Pinned source:** [FluxWitness main at 85b8addf](https://github.com/codebydaksh/FluxWitness/tree/85b8addf874ffb0bf94c5b12166063b125aca6e5). **Prior Lean result:** [B001 CI run #4](https://github.com/codebydaksh/FluxWitness/actions/runs/42715013631), commit \`79a4283b01d6a3c2a3684cb0bf0af00000844a2d\`. The B001 intra-Lean theorem and conditional driver corollary were machine-checked with reported axioms \`propext\`, \`Classical.choice\`, \`Quot.sound\`; the cross-tool assumption was not discharged.

**Scope of this audit:** I read source files, stored WP logs and result metadata from the published repository. I did **not** rerun Frama-C, Rocq or Lean for B002-A; reported WP goal counts come from historical logs. Repository Git blob identities and recorded SHA-256 checksums are not interchangeable. See the machine-readable [premise ledger](B002A_PREMISE_LEDGER.json) for 19 source-anchored assertions.

## A. Dependency graph, not a flat "all proved" claim

\`\`\`text
shipped C heat_step
   | Frama-C/WP contract 103/103, under finite/bounded/separated entry
   v
ACSL heat_heun_fp (C-step postcondition)
   |
   +-- abstract ref_cell(k,j) and ref_update recurrence
   |   driver reference-loop 38/38, UNDER backing/schedule/entry/range/step assumptions
   |
   +-- scalar Euler 5/5
   +-- stage range and average 47/47
          |
          v six imported logical requires clauses
       reference-update WP composition 10/10
          |
          | WP \round_double (nearest-even), \real projection, finite-range
          |     -- CROSS-TOOL NUMERIC SEMANTICS NOT FORMALLY CONNECTED --
          v
  Lean C2 interpretedStep / FloatLib Model.roundAt binary64
          | B001 intra-Lean wpUpdate = interpretedStep (by rfl)
          v
  B001 conditional driver bound (still assumes wp_call_explicit)
\`\`\`

**Critical distinction:** The **10/10** composition is a conditional proof. The six imported properties appear as *requires* clauses in the composition probe. Their separate **5/5** and **47/47** runs are evidence of each property inside WP, but there is no mechanically checked cross-run import in the archived composition. The earlier no-import composition recorded **7/9**, with \`decoded_update\` and \`finite_update\` timing out; that earlier failure must not be conflated with the later conditional 10/10 success.

## B. Exact six WP imported premises

All occur in [composition probe.c](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/evidence/wp-reference-interpretation-08zrp8uz/probe.c#L42-L66).

| Premise | Lines | Supporting recorded WP evidence | Transfer gap |
|---|---:|---|---|
| \`imported_decoded_euler\` | 42–44 | \`compare_euler\`, \`decoded_euler\` Valid, **5/5** | No checked import in composition |
| \`imported_finite_euler\` | 45–46 | \`compare_euler\`, \`finite_euler\` Valid, **5/5** | No checked import |
| \`imported_first_range\` | 47–49 | \`first_bound\`, \`first_range\` Valid, **47/47** combined run | No checked import |
| \`imported_second_range\` | 50–52 | \`second_bound\`, \`second_range\` Valid, **47/47** | No checked import |
| \`imported_decoded_average\` | 53–54 | \`compare_average\`, \`decoded_average\` Valid, **47/47** | No checked import |
| \`imported_finite_average\` | 55–56 | \`compare_average\`, \`finite_average\` Valid, **47/47** | No checked import |

Archived runs:
- [Euler 5/5](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/evidence/wp-reference-interpretation-78nqmvyb/wp.log) (\`result.json\` reports exit 0 and both postconditions Valid).
- [Range and average 47/47](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/evidence/wp-reference-interpretation-tfsopvv2/wp.log).
- [Composed update 10/10](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/evidence/wp-reference-interpretation-08zrp8uz/wp.log).
- [Earlier 7/9 failure](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/evidence/wp-reference-interpretation-_vh9ra7u/wp.log) (two timeouts).

Composition \`result.json\` records source SHA-256 \`231047633ea7001e4c48fce8321bd72ca8f2bf17d9909247da36b56c140d70bc\`, log SHA-256 \`c5c5859ab019adac1085f811e8450928f493cfb86fd66f27682e95b4c01fedad\`. These are **reported archival hashes, not recomputed in this audit**.

## C. Other independent premise boundaries

1. **WP input/reference:** The reference-update theorem assumes \`0 <= k < 223\`, \`0 <= j < 400\` and the entire abstract row \`ref_cell(k,i)\` finite and in [-2,2]. The function \`ref_cell\` is an *uninterpreted logical symbol* in the \`DriverReference\` ACSL block, not a constructed real C trace.
2. **C step:** The [shipped step WP log](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/evidence/wp-shipped-bounded-hy6e4sjy/goals.log) records **103/103** within its separation/finite/range contracts. It does not prove the normal binary calls meet those contracts without entry/lifetime evidence. The log includes a generated-default-spec warning for \`__finite\`; preserve it for reviewers.
3. **Driver:** [ACSL driver wrapper](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/evidence/wp-driver-reference-loop-79is6b47/probe.c#L292-L305) assumes \`backing\`, \`schedule\`, \`entry\`, \`reference_range\`, \`reference_step\`. Its [38/38 log](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/evidence/wp-driver-reference-loop-79is6b47/wp.log) is conditional on all five. The [allocation/slice proof](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/evidence/wp-driver-slices-3u14q3fn/wp.log) is **9/10**, with \`driver_allocate_call_driver_slices_requires_backing\` timed out and warnings on allocation/alignment and casts.
4. **Lean end:** [C2 \`decoded_step_agrees\`](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/lean/C2DecodedStep.lean#L40) equates two **Lean** numerical models under finite/range assumptions. [C3 \`driver223_of_wp\`](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/lean/C3DriverLoop.lean#L18-L35) assumes WP interpretation and abstract calls. B001 replaces these with a specific Lean \`wpUpdate\` and a **still-unproved** \`wp_call_explicit\`.
5. **WP model axioms:** The exported [Cfloat Why3 model](https://github.com/codebydaksh/FluxWitness/blob/85b8addf874ffb0bf94c5b12166063b125aca6e5/rc2/evidence/c2-wp-postcondition-export-20261107/run-mUCtyS/model-cfloat.mlw#L61-L77) defines \`round_double(m,r) = to_f64(F64.round m r)\` and declares \`to_f64_range_round\` as an axiom. The exact finite-range side conditions and the interpretation of WP's rounding as FloatLib's \`Model.roundAt\` are *not proved by B001*.

## D. Smallest next mathematical obligation (not yet a theorem)

For real numerical values at a rounding site in the bounded benchmark, seek independent semantic evidence for:

\`\`\`text
   WP_of_f64 (WP_round_double(WP_RNE, x))
 = Lean_Model_roundAt_binary64(x)
\`\`\`

provided \`x\` is eligible for finite binary64 rounding and any required WP \`F64.in_range\` obligations hold. A proof must identify the common real-number interpretation and finite-range results, not merely replace WP rounding by Lean rounding in the statement. This only compares numeric values: it does not prove signed-zero bits, NaN representation, memory layout, compiled operations, or 223-step execution.

The Lean project already proves \`FluxWitnessC2.binary64_floorEvenGrid\` and \`binary64_round_zero\` for its Floq/FloatLib representation. The WP model has \`F64.round RNE\` and an exported Why3 rounding semantics. The prior trace-premise review describes a Rocq/Flocq nearest-even formula comparison, but its cross-system identification is explicitly external. **Do not count this comparison as a checked bridge.**

### B002-B entry gate

- Pin the specific WP/Why3 and Lean/FloatLib definitions, with source and theorem identifiers.
- State the single-rounding numeric-value relation, plus every domain/range precondition.
- Identify a feasible **mechanically checked**, noncircular proof strategy that does not add the desired equality as an axiom or premise.
- If the strategies require an untrusted ACSL-to-Lean translation, retain it in the ledger instead of asserting closure.
- Only then attempt the smallest scalar proof. Do not modify the frozen RC2 proof tree.

### Stop condition

If no checker-verifiable common rounding semantics is feasible under the current toolchains, mark B002-B **blocked**. The reproducible conditional benchmark and the trust ledger remain valid; running more arbitrary numerical examples does not discharge the semantic relation.

---
**Audit provenance:** all source/proof statuses were read from the repository at the pinned main commit, not freshly checked. A new historical WP run result would require its own explicit compiler/prover environment and hashes.
