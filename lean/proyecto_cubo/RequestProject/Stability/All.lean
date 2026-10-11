module

public import RequestProject.Stability.Basic
public import RequestProject.Stability.PartS
public import RequestProject.Stability.Defs
public import RequestProject.Stability.PartA
public import RequestProject.Stability.PartF
public import RequestProject.Stability.PartT

/-!
# `C44_stability_and_rigidity.md` — Lemma 10.11 (stability) and Theorem 10.12, first half
# (rigidity of the final matrix), for `η = 1` (paper v8 §10.4)

Folder `RequestProject/Stability/`, namespace `Stability`. Nothing listed in the Setting is
redefined. Used directly: C3 `Rulers.oE`, `Rulers.delta`, `Rulers.oE_sdiff`, `Rulers.oE_lt`;
C10 `Deficit.a`, `Deficit.pi0`, `Deficit.Mc`, `Deficit.lemma_4_5`, `Deficit.lemma_4_5_empty`,
`Deficit.A4_subadditivity`; C13 `Dance.slots`, `Dance.slots_eq`, `Dance.mCount`, `Dance.pσ`,
`Dance.κσ`, `Dance.Mfin`, `Dance.dance`; C14 `Windows.Ids`, `Windows.Dset`, `Windows.card_Ids`,
`Windows.Dset_eq_Dlab`, `Windows.Dlab_inj` (the injectivity of the dancers),
`Windows.theorem_4_4`, `Windows.H3_final_matrix`; C32 `Families.ds`; C40 `FormalOps.Bf`;
C40b `FormalDance.Agree`, `MAgree`, `DanceRel`, `finalM`, `paySys`, `ext0`, `L4_sigma`,
`danceRel_unique`; C42 `InvFloors.C109`; C43 `PathSum.piF`, `XiOp`, `SigOp`, `R` (and the
instance `instOddUnitsPadicTwo`, used through `C109`).

## Encodings
* The field is `ℚ_[2]` with its norm (`‖2‖ = 1/2`), so `‖x‖ ≤ 2^{−s}` means `v_2(x) ≥ s`; the
  bound `2^{−s}` is written `(2 : ℝ) ^ (-(s : ℤ))` and `2^{−(α−1)}` is
  `(2 : ℝ) ^ (-(α - 1 : ℤ))`.
* Matrices are Mathlib's `Matrix n n ℚ_[2]` with Mathlib's inverse `M⁻¹` (`Matrix.inv`).
* `hadOne B E := Matrix.of fun i j => B i j * (1 + E i j)` (`B ∘ (1 + E)`), and
  `Wt S ν s := {X | ∀ i j, (¬ S i j → X i j = 0) ∧ ‖X i j‖ ≤ 2^{−(ν i j + s)}}`, exactly as in
  the file (`Basic.lean`).
* `nest ds s s' := Dset ds s' ⊆ Dset ds s`, `Amat ds s s' := if nest ds s s' then
  a_k(D_s ∖ D_{s'}) else 0`, `nuA ds s s' := (Rulers.delta k (D_s ∖ D_{s'})).toNat`, exactly as
  in the file, on `Fin (Dance.slots ds 1)` with `D_s = Windows.Dset ds s` (read through `s.val`)
  and `k = ds.length` (`Defs.lean`).
* Part S: `S` reflexive and transitive and the conditions on `ν` are explicit hypotheses
  `hrefl`, `htrans`, `hνd` (`ν i i = 0`) and `htri` (`ν i j ≤ ν i u + ν u j` when `S i u`,
  `S u j`). The decidability of `S` is not needed (the proofs are classical).
* (F2): `d₁ = F2d1 ds α c`, `d₂ = F2d2 ds α c` (in `ℚ`, cast to `ℚ_[2]`), written exactly as
  in the file with `pi0 = Deficit.pi0 (α : ℤ) c` and `K = 2 ^ ds.length`.
* The `Σ`-side variables are named `YSig`, `GSig` (`Σ` is reserved notation in Lean).

## Where each part is
* (S0) `S0` (`PartS.lean`); (S1) `S1`; (S2) `S2` — for every `s ≥ 1`. In (S1) the inverse of
  `1 + N` lies in `Wt S ν 0` by Cayley–Hamilton (`inv_mem_of_closed`), and `det (1 + N)` is a
  unit by reduction modulo `2` (`norm_det_one_add`).
* (A1) `A1` (`PartA.lean`); (A2) `A2`; (A3) `A3` — for `ds.length ≥ 1`.
* (F1) `F1`; (F2) `F2` (`PartF.lean`). The hypothesis `l ≥ 1` of Part F is not needed for (F1)
  and (F2), and `c ≥ 1` is not needed for (F1); they are left out (more general).
  `F1_gen`, `F2_gen` hold for any digit list `ds`.
* (T1) `T1`; (T2) `T2` (`PartT.lean`), with exactly the hypotheses of the file; all of them are
  used (`B` and the inverses `YΞ`, `YSig` through C43 (R) and C42 (C109)).
-/
