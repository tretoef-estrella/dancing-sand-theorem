module

public import RequestProject.Smith2.Defs
public import RequestProject.Smith2.PartM
public import RequestProject.Smith2.PartZ
public import RequestProject.Smith2.PartG
public import RequestProject.Smith2.PartV
public import RequestProject.Smith2.PartR

/-!
# `C46_smith_form_and_cokernel_over_Z2.md` — Theorem 10.12, second half: the Smith form over `ℤ_2`
# and the cokernel (paper v8 §10.4)

Folder `RequestProject/Smith2/`, namespace `Smith2`. Nothing listed in the Setting is redefined.
Used directly: C40 `FormalOps.Bf` (its ring structure, `Bf.fd`, `Bf.dg`, `tw00`, `tw11`, `tw10`,
`tw01`, `vplus`, `vprime`); C20 `Doubling.dfi`, `Doubling.OddUnits`, `Doubling.isUnit_df`; C40b
`FormalDance.Agree`, `MAgree`, `ext0`, `paySys`, `twP`, `twC`, `twB`, `twD`, `vsplit`,
`CleanStep`, `DanceRel`, `finalM`, `L4_sigma`, `L5`; C40c `FormalAct.sysAct`; C40d
`FormalProp.Q1`, `FormalProp.Q3`; C29 `Filt.T`; C43 `PathSum.XiOp`, `PathSum.piF`; C44
`Stability.nest`, `Stability.length_ds_pos`; C45 `Conjugation.T_eta`; C13 `Dance.slots`,
`Dance.slots_eq`, `Dance.mCount`, `Dance.pσ`, `Dance.κσ`, `Dance.pqCast`; C14 `Windows.Dset`,
`Windows.Ids`, `Windows.finalMatrix`, `Windows.finalMatrix_eq_map`, `Windows.theorem_D_ii`,
`Windows.theorem_D_iii`; C10 `Deficit.Mc`; C32 `Families.ds`; C15 `DanceSmith` (`sl`, `slPerm`,
`P1`, `Mo`, `S1`, `S3`, `floor_minor`, `golden_ceiling`, `smith_of_bounds`, `Cst`, `yHat`,
`xClk`, and the lemmas of the proof of (S2)); C4 `GoldenMatching.cHat`; C16 `FamilyGroup.X`,
`FamilyGroup.SC`, `FamilyGroup.Q`, `FamilyGroup.X1`, `FamilyGroup.L2`, `FamilyGroup.U1`,
`FamilyGroup.piQuotReindex`.

## Encodings
* **Definitions (new)** (`Defs.lean`), exactly as in the file: `Bf.map φ x` (here
  `Smith2.Bf.map`, `(Bf.map φ x).coef m f = φ (x.coef m f)`), `XiOpZ α c η ζ`, and
  `trunc N X i j = ((X i j).appr N : ℤ)`. A matrix over `Bf A` is mapped entrywise,
  `G.map (Bf.map φ)` (Mathlib's `Matrix.map`).
* The coercion `ι : ℤ_[2] →+* ℚ_[2]` of (M5) is Mathlib's `PadicInt.Coe.ringHom`.
* `ds = Families.ds l`, `k = ds.length`, `m = Dance.mCount ds`, `N = 2 ^ m`. The reindexing
  `cs : Fin (2^m) ≃ Fin (Dance.slots ds 1)` is `Fin.cast (slots_cast ds)` (the cast along
  `Dance.slots_eq ds 1` and `one_mul`); `X s s' = finalM GkZ (cs s) (cs s')` is
  `(finalM GkZ).submatrix (Fin.cast (slots_cast _)) (Fin.cast (slots_cast _))`.
* Norms are those of `ℤ_[2]` and `ℚ_[2]`; `‖x‖ = 2^{−n}` is `‖x‖ = (2 : ℝ) ^ (-(n : ℤ))`.
* «`x − y ∈ (2 : ℤ_[2]) ^ N • ⊤`» in (Z0) is stated in the form given by the file in brackets,
  `∃ r, x − y = 2 ^ N * r`; likewise «`X i j − Y i j = 2^N * R i j` for some `R`» in (Z1).
* Exponents written as integers known to be natural are natural numbers `E j` with the equation
  `(E j : ℤ) = …`, as in C15 and C16. Cokernels are `M ⧸ LinearMap.range f`; isomorphisms are
  `Nonempty (… ≃ₗ[ℤ_[2]] …)`; `T ℤ_[2] l` is `Filt.T ℤ_[2] l`, with the action of top `l`.
* The hypothesis of (G1) is written out in (G1), (G2) and (V2) (no new definition is introduced
  for it). Statements with several parts are conjunctions.

## Where each part is
* **Part M** (`PartM.lean`): (M1) `M1`; (M2) `M2`; (M3) `M3`; (M4) `M4`; (M5) `M5`.
* **Part Z** (`PartZ.lean`): (Z0) `Z0`; (Z1) `Z1`; (Z2) `Z2`.
* **Part G** (`PartG.lean`): (G1) `G1`; (G2) `G2`.
* **Part V** (`PartV.lean`): (V1) `V1`; (V2) `V2`.
* **Part R** (`PartR.lean`): (R1) `R1`; (R2) `R2`; (R3) `R3`; (R4) `R4`; (R5) `R5`.

## Hypotheses and generality
* (M3): the clauses «`twP`, `twC`, `twB`, `twD` commute with the map» are stated under the
  hypothesis `[OddUnits A]` of (M2): these blocks are built from `tw10`, `tw11`, `tw00`, `tw01`,
  whose coefficients contain `dfi`, and without it they fail (for `ℤ → ℚ`, `dfi 2` is `0` in `ℤ`
  but `1/3` in `ℚ`). All other clauses of (M3) have no hypothesis.
* (Z2) is stated over any commutative ring and any finite index type.
* (G1): the hypotheses `1 ≤ ds.length` and `1 ≤ i` are kept as in the file but are not needed by
  the re-run (the entry valuations are given).
* Parts V and R use all of (H); `ζ` takes values in `ℤ_[2]`, so `‖ζ j f‖ ≤ 1` (needed by
  `Conjugation.T_eta`) is automatic, and `‖η‖ = 1` follows from `IsUnit η`.
-/
