# C50g — Theorem 10.22 for `i ≥ 1`: the fold law on the even families (paper v8 §10.7)

*Lean piece C50g of the Dancing Sand Theorem. Grepy Escribano, 10 October 2026. Folder `RequestProject/EvenFold/`, namespace `EvenFold`. Do not change any earlier file.*

Paper v8, Theorem 10.22, case `i ≥ 1`: **`X̄(2l + 2, i) ≅ 2X(2l + 2, i)`**.

C50f gives both sides of an even family as glued dances (over `ℤ_[2]`):
- **fold side** (`GlueEven.Q2`): `X̄(2l+2, i) ≅ coker glueOp(Ψ_{i+1}, Ψ_i, Zop) ≅ PF × coker(2^k·M_Ψ)`, with `M_Ψ := finalM (glueC (S4 …) Xk Yk Zk)`;
- **cube side** (`GlueEven.Q3`, `Q4`): `2X(2l+2, i) ≅ coker glueOp(thX − thY, thX + thY, thY) ≅ PF × coker(2^k·M_U)`, with `M_U := finalM (glueC (S4 …) Uk U'k ZUk)`.

The proof shows that `M_U = P·M_Ψ` with `det P` a unit of `ℤ_[2]`. Then the two cokernels are isomorphic.
1. **Each arm (M1).** `Ψ_j` is `XiOpZ 2 c η ζ` with `c = ⌈j/2⌉ ≥ 1` for `j ≥ 1`. Here `η` is a unit and `ζ` is integral (C49 `F5`).
   - Map the two dances to `ℚ_[2]` (C46 `M4`, `M5`).
   - The image of `V := Ψ(Ψ + t)/2` is `BendCor.UOp (image of Ψ) t`.
   - C50e `W3` (`t = ±2`) gives `W'` over `ℤ_[2]` with `det W'` a unit, `W' ≡ 1` modulo 2, and `M_w(V) = W'·M_w(Ψ)` after the map. The map is injective, so the identity holds over `ℤ_[2]`.
   - The arm `U` uses `Ψ_{i+1}` with `t = −2`; the arm `U′` uses `Ψ_i` with `t = +2`.
2. **The glue (M2).** C50 `D3` gives the blocks of both glued final matrices. With `W₋`, `W₊` from (M1), C50e `G5` gives `Z_W = (W₊ − W₋)/2`, and C50e `G4` gives
   `gS W₋ W₊ Z_W · gS X Y Z = gS (W₋X) (W₊Y) Z₁`.
   - Here `2Z₁ = W₊Y − W₋X`.
   - The lower-left block of `M_U` also satisfies `2·ZU = U′ − U = W₊Y − W₋X`.
   - `ℤ_[2]` has no 2-torsion, so `Z₁ = ZU`.

   Hence `M_U = P·M_Ψ` with `P := gS W₋ W₊ Z_W` read through `gE`, and `det P` is a unit (C50e `G3`).
3. **Associates (A).** If `det P` is a unit, then `coker(c·(P·M)) ≅ coker(c·M)`, because `P` maps the range of `c·M` onto the range of `c·(P·M)`.
4. **Assembly (T).** `FoldHalf.A4_even`, then (Q2) at `h = 0`, then (A), then (Q3) at `h = 0` (with the arms of (Q4)), then `FoldCube.V6`.

## Setting (reuse; do not redefine)

- C13 `Dance.slots`; C29 `Filt.T`; C32 `Families.ds`; C16 `FamilyGroup.X`; C38 `FoldGroup.XbarFam`, `FoldGroup.twoM`.
- C39 `FoldHalf.A4_even`, `glueOp`; C39b `FoldCube.V6`.
- C40 `FormalOps.Bf`; C40b `FormalDance.Agree`, `MAgree`, `DanceRel`, `finalM`, `danceRel_unique`.
- C43 `PathSum.XiOp`, `PathSum.piF`, `PathSum.piF_ne_zero`; C45 `Conjugation.I`.
- C46 `Smith2.Bf.map`, `Smith2.XiOpZ`, `Smith2.M1`, `M3`, `M4`, `M5`.
- C49 `FoldOdd.PsiF`, `FoldOdd.kJ`, `FoldOdd.F5`.
- C50 `GlueDance.glueC`, `gE`, `S4`, `PairRel`, `D1`, `D3`; C50c `ArmsEven.*`.
- C50d `Bend.Y0`, `Bend.Nmat`.
- C50e `BendCor.UOp`, `gS`, `W1`, `W3`, `G3`, `G4`, `G5`.
- C50f `GlueEven.ZF`, `PF`, `Q2`, `Q3`, `Q4`.

Throughout:
- `ι := (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])` and `Φ := Smith2.Bf.map ι`;
- a matrix over `Bf ℤ_[2]` is mapped by `Matrix.map · Φ`;
- `ds := Families.ds l`, `ns := Dance.slots ds 1`;
- `h21 : (2 : ℕ) = 2 * 1`.

## Definitions (new)

None.

## Part P — the arms over `ℚ_[2]`

- **(P0) `Ψ_j` over `ℚ_[2]`.** For every `j`:
  `Φ (FoldOdd.PsiF j) = PathSum.XiOp 2 ((j + 1) / 2) ((FoldOdd.kJ j 1 : ℤ_[2]) : ℚ_[2]) (fun m _ => ((FoldOdd.kJ j m : ℤ_[2]) : ℚ_[2]))`, `‖((FoldOdd.kJ j 1 : ℤ_[2]) : ℚ_[2])‖ = 1`, and `‖((FoldOdd.kJ j m : ℤ_[2]) : ℚ_[2])‖ ≤ 1` for all `m`.
- **(P1) The halves over `ℚ_[2]`.** For `X V : Bf ℤ_[2]` and `t : ℤ_[2]` with `(2 : ℤ_[2]) • V = X * (X + t • (1 : Bf ℤ_[2]))`:
  `Φ V = BendCor.UOp (Φ X) ((t : ℤ_[2]) : ℚ_[2])`.

## Part M — the final matrices

- **(M1) One arm.** Let `l j : ℕ` with `1 ≤ j`, and let `t : ℤ_[2]` with `t = 2 ∨ t = -2`. Let `V : Bf ℤ_[2]` with `(2 : ℤ_[2]) • V = FoldOdd.PsiF j * (FoldOdd.PsiF j + t • 1)`. Let `Xk Vk` (matrices over `Bf ℤ_[2]` indexed by `Fin (Dance.slots (Families.ds l) 1)`) satisfy
  `DanceRel (Families.ds l) 1 (fun _ _ => FoldOdd.PsiF j) Xk` and `DanceRel (Families.ds l) 1 (fun _ _ => V) Vk`.
  Then there is `W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1)) ℤ_[2]` with
  - `IsUnit W'.det`;
  - `‖(((W' - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2` for all `s s'`;
  - `finalM Vk = W' * finalM Xk`.
- **(M2) The glue.** Let `n := Dance.slots (Families.ds l) 1`. Let `Xk Yk Zk Uk U'k ZUk` be matrices over `Bf ℤ_[2]` indexed by `Fin n`, with
  `MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)` and `MAgree (U'k - Uk) ((2 : ℤ_[2]) • ZUk)`.
  Let `Wm Wp : Matrix (Fin n) (Fin n) ℤ_[2]` satisfy:
  - `IsUnit Wm.det` and `IsUnit Wp.det`;
  - `‖(((Wm - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1/2` and `‖(((Wp - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1/2` for all `s s'`;
  - `finalM Uk = Wm * finalM Xk` and `finalM U'k = Wp * finalM Yk`.

  Then there is `P : Matrix (Fin (Dance.slots (Families.ds l) 2)) (Fin (Dance.slots (Families.ds l) 2)) ℤ_[2]` with `IsUnit P.det` and
  `finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Uk U'k ZUk) = P * finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk)`.
- **(A) Associates.** For a commutative ring `R`, a `Fintype n` with `DecidableEq`, `M P : Matrix n n R` with `IsUnit P.det`, and `c : R`:
  `Nonempty (((n → R) ⧸ LinearMap.range (c • Matrix.mulVecLin (P * M))) ≃ₗ[R] ((n → R) ⧸ LinearMap.range (c • Matrix.mulVecLin M)))`.

## Part T — Theorem 10.22 for `i ≥ 1`

- **(T) The fold law on the even families, `i ≥ 1`.** For all `l i : ℕ` with `1 ≤ i`:
  `Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i))`.
  (The same form as C49c `ZeroSmith.C5`, the odd families.)

## Proof sketch

- **(P0)**:
  - C49 `F5 j c` gives `PsiF j = Smith2.XiOpZ 2 ((j + 1) / 2) (kJ j 1) (fun m _ => kJ j m)` and `IsUnit (kJ j 1)`.
  - Then C46 `M5`.
  - A unit of `ℤ_[2]` has norm `1` (`PadicInt.isUnit_iff`); every element of `ℤ_[2]` has norm `≤ 1` (`PadicInt.norm_le_one`), and the coercion preserves the norm.
- **(P1)**:
  - Apply `Φ` (a ring hom, C46 `M1`) to the equation: `(ι 2) • Φ V = Φ X * (Φ X + (ι t) • 1)`. This uses `Smith2.Bf.map_smul` and `Φ 1 = 1`.
  - Multiply by `1/2`; `UOp` is `(1/2) • (Ψ * (Ψ + t • 1))`.
- **(M1)**:
  - Map both dances: C46 `M4` (with `OddUnits ℤ_[2]`) gives `DanceRel ds 1 (fun _ _ => Φ (PsiF j)) (Xk.map Φ)`, and likewise for `V`. Use `Matrix.map` of a constant matrix.
  - By (P0) and (P1), these are the dances of `PathSum.XiOp 2 c η ζ` and of `UOp (PathSum.XiOp …) t`, with `c = (j + 1)/2 ≥ 1`.
  - Inverses exist. For `Ψ + t • 1`, `‖t‖ = 1/2` and `Bend.Y0` gives `Y_t`. For `Ψ`, `Conjugation.I` applies, since `PathSum.piF 2 c f ≠ 0` when `c ≥ 1` (`piF_ne_zero`, or `4(f + c) ≠ 0` at every `f` that matters).
  - Apply C50e `W3`, with `B := l + 1`, `α := 2` and the above. It gives `W'` with `W'.map ι = (t/2) • (1 − …)⁻¹`, `IsUnit W'.det`, the congruence, and, through (W2) inside it, `finalM (Vk.map Φ) = W * finalM (Xk.map Φ)`.
  - `finalM (Gk.map Φ) = (finalM Gk).map ι` (C46 `M4`). `ι` is injective (`PadicInt.coe_injective` or `Subtype.coe_injective`). So `finalM Vk = W' * finalM Xk` over `ℤ_[2]`, by `Matrix.map_mul` and `Matrix.ext`.
  - `W3` is stated with `GU` the dance of `UOp`. If the mapped dance's system is only `MAgree` to the constant `UOp` system rather than equal, use `danceRel_unique` (C40b) or rewrite with (P1); here (P1) gives equality.
- **(M2)**:
  - C50 `D3` (with `h := h21`, `r := 1`, `r₂ := 2`) gives the blocks of both final matrices through `gE (S4 …)`:
    - top-left `finalM Xk`, bottom-left `finalM Zk`, bottom-right `finalM Yk`;
    - `2·finalM Zk = finalM Yk − finalM Xk`;
    - the same for the `U` side.
  - C50e `G5` (from the congruences, `‖(Wp − Wm)‖ ≤ 1/2` by the ultrametric inequality) gives `ZW` with `2 • ZW = Wp − Wm`.
  - C50e `G4` gives `Z₁` with `2 • Z₁ = Wp * finalM Yk − Wm * finalM Xk`. The `U`-side lower-left block satisfies the same equation, because `2·finalM ZUk = finalM U'k − finalM Uk = Wp·finalM Yk − Wm·finalM Xk`. No 2-torsion in `ℤ_[2]` gives `Z₁ = finalM ZUk`.
  - Put `P := (gS Wm Wp ZW).submatrix (gE …).symm (gE …).symm` (or `Matrix.reindex`). Then `P * finalM(glue Ψ) = finalM(glue U)` by `G1`/`G4` read through the reindexing (`Matrix.submatrix_mul_equiv`).
  - `IsUnit P.det` by C50e `G3` and `Matrix.det_reindex_self`.
- **(A)**:
  - Let `P` have inverse `P⁻¹` (`Matrix.nonsing_inv`, `IsUnit P.det`). `mulVecLin P` is a linear equivalence `e`.
  - `range (c • mulVecLin (P * M)) = (range (c • mulVecLin M)).map e`, by `Matrix.mulVecLin_mul` and `smul_comp`.
  - Then `Submodule.Quotient.equiv`.
- **(T)**:
  - `FoldHalf.A4_even l i`.
  - Then `GlueEven.Q2 h21 l 0 i`: obtain `Xk Yk Zk`, the `PairRel`, and the equivalence. Rewrite `(2 : ℤ_[2]) ^ 0 • f = f` (`pow_zero`, `one_smul`).
  - `GlueDance.D1` turns the `PairRel` into the two dances `DanceRel … (PsiF (i+1)) Xk` and `DanceRel … (PsiF i) Yk`.
  - `GlueEven.Q4 l i` gives `U U' ZU Uk U'k` with the equations and the `PairRel`. `GlueDance.D1` gives their dances. `GlueEven.Q3 h21 l 0 i …` gives `ZUk` and the cube-side equivalence.
  - (M1) twice:
    - `j := i + 1`, `t := −2`, `V := U` (`PsiF(i+1) − 2•1 = PsiF(i+1) + (−2)•1`), giving `Wm`;
    - `j := i`, `t := 2`, `V := U'` (needs `1 ≤ i`), giving `Wp`.
  - (M2) with these gives `P`. (A), with `c := 2 ^ (0 + (Families.ds l).length)`, identifies the two right factors; `LinearEquiv.prodCongr (LinearEquiv.refl _ _)` keeps `PF l 2 0`.
  - `FoldCube.V6 l i` (an `≃+`), read backwards, closes it. Compose with `LinearEquiv.toAddEquiv`, as in C49c `C5`.

## Checks done before sending

- **Brute force `chkC50g.py`.** It uses the lattice model of `chkC43.py`, with exact rationals, and the series `K(j)` of `chkC49.py`.
  - **(M1)** with the real arms: `Ψ_j` has payment `4(f + ⌈j/2⌉)`, `η = K(j)_1` and `ζ_m = K(j)_m`, for `1 ≤ j ≤ 7` and every `l ≤ 7`. With `t = ±2` and `V = Ψ(Ψ + t)/2`, the matrix `W = M_w(V)·M_w(Ψ)⁻¹` is integral, `≡ I` modulo 2, with `det W` a unit, and `W·M_w(Ψ) = M_w(V)` exactly. `M_w(Ψ)` is integral.
  - **(M2)** and **(A)** on 300 random integer matrices, sizes `1..4`:
    - the glue identity holds and its determinant is a unit;
    - `Smith(P·M) = Smith(M)`, and also after multiplying by `4`.
  - **1 490 checks, 0 failures.** Log `logs/chkC50g.log`. `v_2(W − I) = 1` occurs (62 times).
- **Controls (all four fire):**
  - `j = 0`: the shift is `0` and `Ψ_0` is singular on `T(l)`. This is why `i = 0` is C50h.
  - `W ≡ I` modulo 4: it fails.
  - (A) with an even `det P`: the Smith form changes.
  - `t = ±4`: `W` is not integral, or not `≡ I` modulo 2.
- **Theorem 10.22 itself, numerically:** `chkC50f.py` already checked that the Smith forms of the two glued operators agree for every `l ≤ 6`, `1 ≤ i ≤ 6`.

## Notes

- After this piece:
  - C50h: Theorem 10.22 at `i = 0`, by congruences, as C49b did (`Ψ_0` is not invertible; replace the shift by a parameter `c = 2^n` and pass to the limit through congruences of the final matrices);
  - C51: Theorem DW;
  - C52: the odd parts.
- (A) is stated over any commutative ring; C51 may reuse it.
