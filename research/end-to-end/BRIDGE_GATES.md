# End-to-end bridge gate: concrete next obligations

**Research only. This file is a specification of missing work, not a theorem or an
assertion that the trusted boundary has closed.** Frozen main and RC2 are not modified.

## Verified inputs and remaining facts

1. `rc2/lean/C2RoundingConstruction.lean` proves FloatLib rounding equals
   `floorEvenGrid` under explicit exponent bounds (and zero is handled).
   It does **not** prove Why3's `F64.round RNE` denotes that same function.
2. `rc2/evidence/c2-wp-postcondition-export-20261107/run-mUCtyS/model-cfloat.mlw`
   defines `round_double(m,x)=to_f64(F64.round m x)` and contains
   `to_f64_range_round`, an **axiom in the imported WP model**.
   It gives the projected real result only under `F64.in_range x`.
3. `rc2/lean/C2DecodedStep.lean` proves a Lean transcribed update equals the
   rounded reference under finite and range premises. It does **not**
   establish source-language semantics for ACSL or C.
4. `research/assumption-hunter/WPInterpretationBridge.lean` in research B001
   proves equality of two manually transcribed Lean expressions via `rfl`.
   Its `wp_call_explicit` is still a hypothesis, not a proved C transition.
5. `rc2/evidence/wp-driver-reference-loop-79is6b47/probe.c` and log prove
   38/38 for a **conditional** reference-row driver.
6. `rc2/evidence/wp-driver-slices-3u14q3fn/wp.log` proves 9/10 for an
   allocation probe. The unresolved goal is
   `typed_driver_allocate_call_driver_slices_requires_backing`. The log
   explicitly warns about allocation, alignment, and the byte-to-double cast.

## Gate S1: WP rounding projection to FloatLib rounding

At **one** Euler rounding site, on a finite bounded input from the
benchmark, establish the following semantic bridge:

- WP side: `of_f64(round_double(RNE,x))`.
- Lean side: `Model.roundAt binary64 x` (via `floorEvenGrid`).
- Requested result: numerical equality, with a mechanically documented
  meaning for the *same* `x` and the real-value domains, plus a proved
  in-range premise for the WP conversion.
- Distinguish equality of real numerical values from signed-zero bit identity.

**Pass gate:** independently checked formal artifact resolving the mapping
of the Why3/Flocq and Lean reals, rounding and representation *without
postulating their equality*. Evidence must specify each trusted import and
its kernel/prover scope.

**Fail gate:** another theorem only comparing two Lean redefinitions, an
unproved `axiom`, `sorry`, an admitted statement, an external prose
comparison, or a finite sample check. Existing external floor-even comparison
is useful, but is not a kernel-checked cross-system equality.

**Feasibility stop:** if a mechanically accepted cross-language mapping is
not practical, stop and state the semantic equality as an explicit, quantified
trusted assumption in the publication ledger. Do not claim it discharged.

## Gate S2: actual C call state to abstract row

Construct the state interpretation for one *successful* `heat_step` call:

- Concrete entry has a valid, aligned writable allocation of **1200 doubles**
  split into three disjoint 400-cell slices `u, L, U1`.
- The 400 entries in `u` must be finite and in the benchmark range.
- The call uses the stored `dt`, `dx2` and stencil constants; the C call
  returns success without freeing/reallocating the backing memory.
- At each cell, the post-state `u[i]` decodes to the same real as the
  reference `ref_update` for the pre-state row.
- Required induction interface: a *concrete, representation-preserving*
  instance of `wp_call_explicit` in
  `research/assumption-hunter/WPInterpretationBridge.lean`, not a restatement
  of the hypothesis.

**Pass gate:** verified C preconditions and post-state correspondence for one
real call, with allocation, lifetime, aliasing, indexing, numerical decoding,
and source schedule identified. A separate WP proof of conditional disjoint
slices alone is insufficient; malloc/cast backing remains an open obligation.

**Fail gate:** assume `live` or `wp_call_explicit` with an arbitrary type
`S`, reuse a hand-written reference transition as the C call, or infer
runtime behavior from 38/38 conditional goals.

## Gate S3: 223-call composition and actual initialization

Only after S1/S2, prove the trace has 223 successful transitions, and
the entry state matches the initial-grid certificate for the **same** run.
Use `FluxWitnessC3.driver223_of_wp` or a proved specialization, explicitly
tracking original compiler flags, libm and runtime environment.

**Stop rules:** no edits to `main`, frozen RC2, or existing verified research
lemmas; no `sorry`, new proof axioms, shortened C path, relaxed numeric
bounds or replacement of actual C memory by a fictional state. Each gate gets
a standalone artifact and independent verification log. Negative findings
must remain visible.

## Immediate prioritized experiment

**Prioritize S2a**: a caller-supplied preallocated 1200-double buffer
function, proved under a *documented caller backing contract*, which
establishes the three slices' validity, disjointness and preservation across
one successful call. This is a narrow *conditional* state proof and avoids
claiming that `malloc` provides the 1200-double typed block.
S2b must later discharge that caller backing condition for the actual
allocation and initialization. S1 is the parallel numerical-semantic track.

Do not publish a percentage toward end-to-end verification from any WP goal
count or number of discharged scalar imports.
