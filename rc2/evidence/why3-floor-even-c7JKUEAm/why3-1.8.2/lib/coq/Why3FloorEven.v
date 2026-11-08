From Coq Require Import Reals ZArith Lra.
From Flocq Require Import Core.Core.
Require Why3.ieee_float.Float64.
Open Scope R_scope.

Definition floor_even_index (y : R) : Z :=
  let n := Zfloor y in
  match Rcompare (y - IZR n) (/2) with
  | Lt => n
  | Gt => (n + 1)%Z
  | Eq => if Z.even n then n else (n + 1)%Z
  end.

Lemma nearest_index_agrees y : ZnearestE y = floor_even_index y.
Proof.
  unfold floor_even_index, Znearest.
  destruct (Rcompare_spec (y - IZR (Zfloor y)) (/2)) as [H|H|H].
  - reflexivity.
  - rewrite Zceil_floor_neq by lra.
    destruct (Z.even (Zfloor y)); reflexivity.
  - apply Zceil_floor_neq; lra.
Qed.

Definition floor_even_grid (e : Z) (x : R) : R :=
  let k := Z.max (e - 53) (-1074) in
  IZR (floor_even_index (x * bpow radix2 (-k))) * bpow radix2 k.

Theorem why3_binary64_floor_even_grid (e : Z) (x : R) :
  x <> 0 ->
  bpow radix2 (e-1) <= Rabs x < bpow radix2 e ->
  Why3.ieee_float.Float64.round Why3.ieee_float.RoundingMode.RNE x = floor_even_grid e x.
Proof.
  intros _ Hbinade.
  change (Generic_fmt.round radix2 (FLT_exp (-1074) 53) ZnearestE x = floor_even_grid e x).
  unfold Generic_fmt.round, scaled_mantissa, F2R.
  cbn [Fnum Fexp].
  rewrite (cexp_fexp radix2 (FLT_exp (-1074) 53) x e Hbinade).
  unfold floor_even_grid, FLT_exp.
  rewrite nearest_index_agrees. reflexivity.
Qed.

Theorem why3_binary64_zero :
  Why3.ieee_float.Float64.round Why3.ieee_float.RoundingMode.RNE 0 = 0.
Proof.
  change (Generic_fmt.round radix2 (FLT_exp (-1074) 53) ZnearestE 0 = 0).
  apply round_0; typeclasses eauto.
Qed.

Print Assumptions why3_binary64_floor_even_grid.
Print Assumptions why3_binary64_zero.
