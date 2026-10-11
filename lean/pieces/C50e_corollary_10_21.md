# C50e — Corollary 10.21: the two halves of `Ψ(Ψ ± 2)` (paper v8 §10.7)

*Lean piece C50e of the Dancing Sand Theorem. Grepy Escribano, 10 October 2026. Folder `RequestProject/BendCor/`, namespace `BendCor`. Do not change any earlier file.*

Paper v8, Corollary 10.21. In the setting of Lemma 10.20 (C50d), the paper says:
- the dances of `Ψ(Ψ ± 2)/2` are clean;
- **`M_w(Ψ(Ψ + 2)/2) = W_+·M_w(Ψ)`** and **`M_w(Ψ(Ψ − 2)/2) = W_−·M_w(Ψ)`**;
- **`W_± ∈ ±I + 2·Mat(ℤ_2)`**.

Cleanliness was proved in C50c (`ArmsEven.H1`, `E1`). This piece proves the identity and the congruence over `ℚ_[2]`, with norms, for one shift `t` with `‖t‖ = 1/2` (the paper's `t = ±2`). It also proves the scalar facts about `glue(W_−, W_+)` that Theorem 10.22 uses.

**The idea.**
1. **Partial fractions.** `Ψ` and `Ψ + t` commute, because `t • 1` is central (C40 `Bf.smul_mul`, `Bf.mul_smul`). Put `U_t := (1/2)·Ψ(Ψ + t)`. If `Y` inverts `Ψ` and `Y_t` inverts `Ψ + t` (both sides, in the `Agree` sense), then `(2/t)(Y − Y_t)` inverts `U_t` on both sides:
   - `U_t·Y ≈ (1/2)(Ψ + t)` and `U_t·Y_t ≈ (1/2)Ψ`;
   - the difference is `t/2`.
2. **The final matrices.** By C50d `Nmat_eq_inv`, `(finalM G_U)⁻¹ = Nmat((2/t)(Y − Y_t))`. `Nmat` is linear in `Y`, so this is `(2/t)((finalM G_Ψ)⁻¹ − N_t)`, with `N_t := Nmat Y_t`. Hence
   `(finalM G_U)⁻¹ = (2/t)·(finalM G_Ψ)⁻¹·(1 − E)`, with `E := finalM G_Ψ · N_t`,
   and `finalM G_U = W·finalM G_Ψ`, with `W := (t/2)·(1 − E)⁻¹`.
3. **The congruence.** By C50d `B1`, every entry of `E` has norm `≤ 1/2`. For such an `E`:
   - `det(1 − E)` has norm `1`;
   - `(1 − E)⁻¹` has integral entries and is `≡ 1` modulo `2`.

   Since `‖t/2‖ = 1`, `t/2` is an odd unit, so `W ≡ 1` modulo `2`, and `det W` has norm `1`. (Modulo `2`, `−1 ≡ 1`: the paper's `±I` is the same class.)

## Setting (reuse; do not redefine)

- C13 `Dance.slots`; C32 `Families.ds`; C29 `Filt.T`.
- C40 `FormalOps.Bf`: its `Ring`, `Algebra ℚ_[2]` (`Bf.instAlgebra`), `Bf.smul_mul`, `Bf.mul_smul`, `coef`.
- C40b `FormalDance.Agree` (`Agree.refl`, `symm`, `trans`, `add`, `sub`, `mul`, `smul`, `of_eq`), `DanceRel`, `finalM`.
- C42 `InvFloors.C109` (`IsUnit (finalM Gk).det`).
- C43 `PathSum.XiOp`, `PathSum.piF`, `PathSum.norm_two_padic`, `instOddUnitsPadicTwo`.
- C50d `Bend.Nmat`, `Bend.Nmat_apply`, `Bend.N2`, `Bend.Nmat_eq_inv`, `Bend.Y0`, `Bend.B1`.

Throughout:
- the field is `ℚ_[2]`;
- `ns := Dance.slots (Families.ds l) 1`; matrices are `Matrix (Fin ns) (Fin ns) ℚ_[2]`;
- `1` is the identity matrix.

## Definitions (new)

- `UOp (Ψ : Bf ℚ_[2]) (t : ℚ_[2]) : Bf ℚ_[2] := (1 / 2 : ℚ_[2]) • (Ψ * (Ψ + t • (1 : Bf ℚ_[2])))`.
- `gS {R : Type*} [Ring R] {n : Type*} (X Y Z : Matrix n n R) : Matrix (Fin 2 × n) (Fin 2 × n) R`, the scalar glue `[[X, 0], [Z, Y]]`. It is written exactly like C50 `GlueDance.glueM`:
  `gS X Y Z p p' := if p.1 = 0 ∧ p'.1 = 0 then X p.2 p'.2 else if p.1 = 1 ∧ p'.1 = 0 then Z p.2 p'.2 else if p.1 = 1 ∧ p'.1 = 1 then Y p.2 p'.2 else 0`.

## Part A — partial fractions

- **(A0) `t • 1` is central.** For `t : ℚ_[2]` and `x : Bf ℚ_[2]`: `(t • (1 : Bf ℚ_[2])) * x = x * (t • (1 : Bf ℚ_[2]))`. Also `Ψ * (Ψ + t • 1) = (Ψ + t • 1) * Ψ`.
- **(A1) The inverse of `U_t`.** Let `Ψ Y Y_t : Bf ℚ_[2]` and `t ≠ 0`, with
  `Agree (Ψ * Y) 1`, `Agree (Y * Ψ) 1`, `Agree ((Ψ + t • 1) * Y_t) 1`, `Agree (Y_t * (Ψ + t • 1)) 1`.
  Then `Agree (UOp Ψ t * ((2 / t) • (Y - Y_t))) 1` and `Agree (((2 / t) • (Y - Y_t)) * UOp Ψ t) 1`.
- **(A2) `Nmat` is linear.** For all `l B`, `Y Y'` and `a : ℚ_[2]`:
  `Bend.Nmat l B (Y + Y') = Bend.Nmat l B Y + Bend.Nmat l B Y'`, `Bend.Nmat l B (Y - Y') = Bend.Nmat l B Y - Bend.Nmat l B Y'`, `Bend.Nmat l B (a • Y) = a • Bend.Nmat l B Y`.

## Part F — the final matrices

Let `l B : ℕ` with `l + 1 ≤ B`, and let `Ψ Y Y_t`, `t ≠ 0` be as in (A1). Let `GΨ` and `GU` (matrices over `Bf ℚ_[2]` indexed by `Fin ns`) satisfy
`DanceRel (Families.ds l) 1 (fun _ _ => Ψ) GΨ` and `DanceRel (Families.ds l) 1 (fun _ _ => UOp Ψ t) GU`.
Put `E := finalM GΨ * Bend.Nmat l B Y_t`.

- **(F1)** `(finalM GU)⁻¹ = (2 / t) • ((finalM GΨ)⁻¹ - Bend.Nmat l B Y_t)`.
- **(F2)** `IsUnit (1 - E).det`, and `finalM GU = ((t / 2) • (1 - E)⁻¹) * finalM GΨ`.

## Part W — the congruence

- **(W1) Near the identity.** Let `n` be a `Fintype` with `DecidableEq`, and `E : Matrix n n ℚ_[2]` with `‖E i j‖ ≤ 1/2` for all `i j`. Then:
  - `‖(1 - E).det‖ = 1`;
  - `‖(1 - E)⁻¹ i j - (1 : Matrix n n ℚ_[2]) i j‖ ≤ 1/2` for all `i j`;
  - `‖(1 - E)⁻¹ i j‖ ≤ 1` for all `i j`.
- **(W2) Corollary 10.21.** Let `l : ℕ` (any), `B ≥ l + 1`, `α ≥ 2`, `c ≥ 1`, `η` with `‖η‖ = 1`, `ζ` with `‖ζ m f‖ ≤ 1` for `m ≥ 2`, and `t` with `‖t‖ = 1/2`. Let `Ψ := PathSum.XiOp α c η ζ`. Let `Y`, `Y_t` be two-sided inverses (in the `Agree` sense) of `Ψ` and `Ψ + t • 1`. Let `GΨ`, `GU` be as in Part F. Put `W := (t / 2) • (1 - finalM GΨ * Bend.Nmat l B Y_t)⁻¹`. Then:
  - `finalM GU = W * finalM GΨ`;
  - `‖W s s' - (1 : Matrix _ _ ℚ_[2]) s s'‖ ≤ 1/2` for all `s s'`;
  - `‖W s s'‖ ≤ 1` for all `s s'`;
  - `‖W.det‖ = 1`.
- **(W3) The integral form.** In the setting of (W2), there is `W' : Matrix (Fin ns) (Fin ns) ℤ_[2]` with `W'.map (fun z : ℤ_[2] => (z : ℚ_[2])) = W`, with `IsUnit W'.det`, and with `‖((W' s s' : ℤ_[2]) : ℚ_[2]) - (1 : Matrix _ _ ℚ_[2]) s s'‖ ≤ 1/2` for all `s s'`.
- **(W4) Both signs, as in the paper.** In the setting of (W2) without `t`, let `Y₊`, `Y₋` be two-sided inverses of `Ψ + (2 : ℚ_[2]) • 1` and `Ψ + (-2 : ℚ_[2]) • 1`. Let `GU₊`, `GU₋` satisfy `DanceRel (Families.ds l) 1 (fun _ _ => UOp Ψ 2) GU₊` and `DanceRel (Families.ds l) 1 (fun _ _ => UOp Ψ (-2)) GU₋`. Put
  `W₊ := (1 - finalM GΨ * Bend.Nmat l B Y₊)⁻¹` and `W₋ := -(1 - finalM GΨ * Bend.Nmat l B Y₋)⁻¹`.
  Then `finalM GU₊ = W₊ * finalM GΨ`, `finalM GU₋ = W₋ * finalM GΨ`, `‖W₊ s s' - (1 : Matrix _ _ ℚ_[2]) s s'‖ ≤ 1/2` and `‖W₋ s s' + (1 : Matrix _ _ ℚ_[2]) s s'‖ ≤ 1/2` for all `s s'`.

## Part G — the scalar glue

- **(G1) Product.** For any ring `R` and any `Fintype n` with `DecidableEq`: `gS X Y Z * gS X' Y' Z' = gS (X * X') (Y * Y') (Z * X' + Y * Z')`.
- **(G2) Determinant.** For any commutative ring `R`: `(gS X Y Z).det = X.det * Y.det`.
- **(G3) Units.** Over `ℤ_[2]`: if `IsUnit X.det` and `IsUnit Y.det`, then `IsUnit (gS X Y Z).det`, for every `Z`.
- **(G4) The paper's identity.** Over `ℤ_[2]`, let `X Y Z W₋ W₊ Z_W` satisfy `2 • Z = Y - X` and `2 • Z_W = W₊ - W₋`. Then `gS W₋ W₊ Z_W * gS X Y Z = gS (W₋ * X) (W₊ * Y) Z₁` for some `Z₁` with `2 • Z₁ = W₊ * Y - W₋ * X`. (This is the paper's `glue(W₋, W₊)·glue(X, Y) = glue(W₋X, W₊Y)`.)
- **(G5) The half exists.** Over `ℤ_[2]`, if `‖((W₊ - W₋) s s' : ℚ_[2])‖ ≤ 1/2` for all `s s'`, then there is `Z_W` with `2 • Z_W = W₊ - W₋`.

## Proof sketch

- **(A0)**: `Bf.smul_mul` and `Bf.mul_smul` (`t • 1 * x = t • x = x * t • 1`). Then expand `Ψ * (Ψ + t • 1)` with `mul_add`/`add_mul`.
- **(A1)**: by (A0), `UOp Ψ t = (1/2) • ((Ψ + t • 1) * Ψ)`.
  - `UOp * Y = (1/2) • ((Ψ + t • 1) * (Ψ * Y))`, which agrees with `(1/2) • (Ψ + t • 1)` (`Agree.mul` with `Agree.refl`, then `Agree.smul`).
  - `UOp * Y_t = (1/2) • (Ψ * ((Ψ + t • 1) * Y_t))`, which agrees with `(1/2) • Ψ`.
  - So `UOp * ((2/t) • (Y - Y_t))` agrees with `(2/t) • (1/2) • (t • 1) = 1`, using `Agree.sub` and `Agree.smul`.
  - The other side is the same with `(Y * Ψ)` and `(Y_t * (Ψ + t • 1))`.
- **(A2)**: by `Bend.Nmat_apply` (or `Bend.N2` when `B ≥ l + 1`).
  - `sysAct` is linear in the system: on a constant `1 × 1` system it is C40c's action of the single entry, and C40 `act` is additive and commutes with scalars.
  - If that is awkward, use the closed entry formula `Bend.N2`, which is linear in `Y.coef`. In that case state (A2) with `l + 1 ≤ B`. **Tell me if you do.**
- **(F1)**: `Bend.Nmat_eq_inv` twice:
  - for `Ψ` with `Y`;
  - for `UOp Ψ t` with `(2/t) • (Y - Y_t)`, by (A1).

  Then (A2).
- **(F2)**:
  - `InvFloors.C109` gives `IsUnit (finalM GΨ).det` and `IsUnit (finalM GU).det`.
  - Write `M := finalM GΨ`. Then `(2/t) • (M⁻¹ - N_t) = (2/t) • M⁻¹ * (1 - M * N_t)`.
  - So `(1 - E) = (t/2) • (M * (finalM GU)⁻¹)` is a unit.
  - Then `finalM GU = ((2/t) • M⁻¹ * (1 - E))⁻¹ = (t/2) • (1 - E)⁻¹ * M` (`Matrix.mul_inv_rev`, `Matrix.inv_smul`).
- **(W1)**:
  - **The determinant.** `det(1 - E) = Σ_σ sign σ ∏_i (1 - E)_{σ i, i}`. The identity term is `∏(1 - E_ii)`, which is `≡ 1`. Every other term has at least one off-diagonal factor, of norm `≤ 1/2`, and the rest have norm `≤ 1`. So `‖det(1 - E) - 1‖ ≤ 1/2`, hence `‖det‖ = 1`.
  - Alternatively, induct on `n` with `Matrix.det_succ_column_zero`, or map to `ℤ_[2]` and then to `ZMod 2`, where `E ↦ 0`.
  - **The inverse.** The entries of the adjugate are polynomials with integer coefficients in entries of norm `≤ 1`, so they have norm `≤ 1`. Then `(1 - E)⁻¹ = (det)⁻¹ • adjugate` has entries of norm `≤ 1`.
  - Then `(1 - E)⁻¹ - 1 = (1 - E)⁻¹ * E` (from `(1 - E)⁻¹ * (1 - E) = 1`). Each entry is a sum of products of norm `≤ 1·(1/2)`; use the ultrametric inequality (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, as in C50d `B1_pos`).
- **(W2)**: (F2), with `‖E s s'‖ ≤ 1/2` from `Bend.B1` (its hypotheses are exactly those listed).
  - `t ≠ 0` from `‖t‖ = 1/2`.
  - `‖t / 2‖ = 1` (`PathSum.norm_two_padic`).
  - `W - 1 = (t/2) • ((1 - E)⁻¹ - 1) + (t/2 - 1) • 1`, and `‖t/2 - 1‖ ≤ 1/2`, because `t/2` is a unit of `ℤ_[2]` and every unit of `ℤ_[2]` is odd (`PadicInt.norm_lt_one_iff_dvd` or `ZMod 2` reduction).
  - `‖W.det‖ = ‖t/2‖^ns · ‖(1 - E)⁻¹.det‖ = 1`.
- **(W3)**: each entry has norm `≤ 1`, so it lies in `ℤ_[2]` (`PadicInt.mk` / `⟨x, h⟩`). The determinant commutes with the ring map `ℤ_[2] → ℚ_[2]` (`RingHom.map_det`), and a `ℤ_[2]` element of norm `1` is a unit (`PadicInt.isUnit_iff`).
- **(W4)**: (W2) at `t = 2` (`W = W₊`) and at `t = -2` (`W = -(…)⁻¹ = W₋`). `‖W₋ + 1‖ ≤ 1/2` is `‖-(W₋' - 1)‖`, with `W₋' := (1 - …)⁻¹`, by (W1).
- **(G1)**: unfold `gS` and `Matrix.mul_apply`. Use `Fintype.sum_prod_type` over `Fin 2 × n`, then `Fin.sum_univ_two`, and case on the two indices.
- **(G2)**: reindex to `Matrix.fromBlocks X 0 Z Y` along `Fin 2 × n ≃ n ⊕ n` (`finTwoArrowEquiv`-style, or `Equiv.sumEquivSigmaBool`), then `Matrix.det_fromBlocks_zero₁₂`. Or reuse whatever C50 `GlueDance` already proves about `glueM`.
- **(G3)**: (G2) and `IsUnit.mul`.
- **(G4)**: (G1) gives `Z₁ = Z_W * X + W₊ * Z`, and then
  `2 • Z₁ = (W₊ - W₋) * X + W₊ * (Y - X) = W₊ * Y - W₋ * X`.
- **(G5)**: each entry of `W₊ - W₋` has norm `≤ 1/2`, so it is divisible by `2` in `ℤ_[2]` (`PadicInt.norm_le_pow_iff_dvd` or `PadicInt.mem_span_pow_iff_le_valuation`). Choose the quotients.

## Checks done before sending

- **Brute force `chkC50e.py`.** It builds on `chkC43.py`: an independent lattice model of `T(l)` with exact rationals.
  - The final matrices are computed as `2^k O G^{−1} I` (C41 (V5)).
  - `Nmat` is computed directly as `2^k O·act(Y)·I`.
  - `Y`, `Y_t` are the right inverses from the recursion.
  - The parameters:
    - every `l ≤ 7` (`l = 0` included);
    - `α = 2, 3` and `c = 1, 2, 3, 4`;
    - `η` a random unit;
    - `ζ` zero, constant, or depending on `f`;
    - `t ∈ {2, −2, 6, 2/3, −10/7}`.
  - Checked:
    - (A1), both sides, against `1` on every `m ≤ f`;
    - `Nmat Y = M_w(Ψ)⁻¹` (the model of `Nmat_eq_inv`);
    - `Nmat` of `Y_t` two ways;
    - (A2);
    - (F1) and (F2) exactly;
    - (W2): `W` integral, `W ≡ I` mod 2, `det W` a unit.
  - (W1) on 400 random `E` with even entries, sizes `1..6`.
  - (G1), (G2), (G3), (G4) on 300 random integer matrices, sizes `1..4`.
  - **8 253 checks, 0 failures.** Log `logs/chkC50e.log`. `v_2(W − I) = 1` occurs (203 times with `t = ±2`), so the congruence is sharp.
- **Controls (all six fire):**
  - `U` without the `1/2`: (F1) fails.
  - The inverse with the wrong sign, `(2/t)(N_t − M⁻¹)`: (F1) fails.
  - `W ≡ I` modulo `4`: it fails.
  - `α = 1`: `W` is not `≡ I` mod 2 (or not integral) somewhere.
  - (W1) with one odd entry: it fails.
  - (G4) with the products in the wrong order (`Y W₊ − X W₋`): it fails.

## Notes

- §10.7 after this piece:
  - C50f: Theorem 10.22 for `i ≥ 1`. It assembles C50c (the arms and `U`, `U′` as covariant systems), C50 (`PairRel`, the glue), this piece, Proposition 10.7 (C40d) for the glued size-2 system, and Lemma 10.5 (C39, C39b) for the even families.
  - C50g: `i = 0`, by congruences, as C49b did for the odd families.
- (W1) is stated for any finite index type; C50f will use it for the glued matrix too.
