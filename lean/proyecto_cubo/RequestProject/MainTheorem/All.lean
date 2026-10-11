module

public import RequestProject.MainTheorem.Shape
public import RequestProject.MainTheorem.Group
public import RequestProject.MainTheorem.Theorem

/-!
# `C33_the_main_theorem.md` — the Main Theorem (the Dancing Sand Theorem)

Folder `RequestProject/MainTheorem/`, namespace `MainTheorem`.  Nothing listed in the Setting is
redefined: C3 `Rulers.lam`, `Rulers.oE`, `Rulers.clock` (through `Rulers.xi` and C16's pooled
clocks), C7 `TheoremF.dancer`, `lemma_0b`, `lemma_0c_existsUnique`, C13 `Dance.mCount`, C14
`Windows.Ids`, `card_Ids`, C16 `FamilyGroup.X`, `SC`, `Q`, `yPool`, `yPool0`, `T1`, `T2`,
`T2_empty`, C17 `CubeLaplacian.K`, `Syl2`, C31 `FamDec.L`, `m`, `M3`, `L1`, `L2` and C32
`Families.ds`, `ds_zero`, `B0b`, `T2`, `T3` are used directly.

## Encodings

* `ℤ_[2]` is `PadicInt 2`; `λ` is written `lam`.
* `k λ = (ds λ).length`, `I λ = Windows.Ids (ds λ)` (a `Finset ℕ`), `N λ = 2 ^ Dance.mCount (ds λ)`
  are written out in the statements.
* `XFam lam i` (G0) is a type defined by cases on `i`, with its product module structure; products
  over positions are dependent function types over `Fin N` (resp. `Fin (N − 1)`), and the integer
  exponents are made natural by `Int.toNat`.
* «`X ≅ Y`» is `Nonempty (X ≃ₗ[ℤ_[2]] Y)` (Parts S, G) or `Nonempty (X ≃+ Y)` (Part M); explicit
  equivalences `S4equiv`, `G2equiv`, `M1equiv`, `M2equiv` are also given.

## Index

* **Part S** (`Shape.lean`): (S1) `S1_lam`, `S1_oE`, `S1_succ` (and `S1_xi`); (S2) `S2`,
  `S2_length`; (S3) `S3_subset`, `S3_card`; (S4) `S4`, `S4_Q0`; (S5) `S5_order`, `S5_zero`,
  `S5_unique`.
* **Part G** (`Group.lean`): (G0) `XFam` (with `XFam_zero`, `XFam_succ`); (G1) `G1_pos`,
  `G1_zero`; (G2) `G2`.
* **Part M** (`Theorem.lean`): (M1) `M1`; (M2) `M2`; (M3) `M3_support`, `M3_shift`, `M3_self`,
  `M3_zero`.

Unused hypothesis: in (M3), `FamDec.m n n = 1` holds for every `n`; the hypothesis `1 ≤ n` of
`M3_self` is kept as in the file.
-/
