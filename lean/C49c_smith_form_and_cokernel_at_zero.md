# The Smith form and the cokernel of Ξ at c = 0; Theorem 10.16 and Corollary 10.17 for every index (paper v8 §10.6, second half)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §10.6, end of the proof of Theorem 10.16 (the case `c = 0`) and Corollary 10.17.

C49b gave the data at `c = 0`: entry by entry, the final matrix of `Ξ_0` has the zeros and the 2-adic valuations of the integer matrix `M^{(α)}(l, 0)` (C49b (V1), (V2)), and a zero row, hence determinant `0` (C49b (V3)). This piece finishes the case:
- the Smith form of C15 (Z3), which has one zero entry, depends only on the support and the entry valuations (as C46 Part G did for C15 (S3));
- a truncation lemma with one zero diagonal entry, using `det = 0`;
- the final matrix of `Ξ_0` is equivalent over `ℤ_[2]` to `M^{(α)}(l, 0)`, so the cokernel of `Ξ_0` on `T(l)` is `X^{(α)}(l, 0)`;
- Theorem 10.16 for every `c`, and Corollary 10.17 for every `l` and every `j`.

Folder `RequestProject/ZeroSmith/`, namespace `ZeroSmith`. Nothing of the project is redefined.

## Setting (reused, without changing them)

- C40 `FormalOps`: `Bf`. C40b `FormalDance`: `DanceRel`, `finalM`. C40c `FormalAct.sysAct`; C40d `FormalProp.Q1`.
- C13 `Dance`: `slots`, `mCount`, `PQ`, `pqCast`. C14 `Windows`: `finalMatrix`, `Dset`, `theorem_D_ii`.
- C15 `DanceSmith`: `sl`, `sl_sl`, `slPerm`, `P1`, `Mo`, `Mo_eq_mul`, `submatrix_perm_eq`, `odd_det_permMatrix`, `zeroPos`, `final_row_zero`, `Z1`, `Z_val`, `Z_floor`, `Z_ceil`, `Z_main`, `Z3`, `yHatS`, `yHatS_eq`, `yHatS_succ`, `smith_of_bounds`, `floor_minor`, `golden_ceiling`, `lastSet`, `firstSet`, `dancer_eq_empty_iff`, `two_pow_padicValInt_dvd`, `not_two_pow_succ_dvd`, `Ids`.
- C8 `Potential.cHat`; C6 `Houses.cHatH`; `TheoremF.dancer_zero`.
- C16 `FamilyGroup`: `X`, `SC`, `Q`, `X_equiv_coker`, `L1`, `L2`, `piQuotReindex`.
- C46 `Smith2`: `trunc`, `Z0`, `Z1`, `Z2`, `XiOpZ`, `slots_cast`, `smith_reindex`, and the model of Part G (`G_floor`, `G_ceil`, `G_main`, `G1`) and of (R4).
- C48b `DanceXi`: (T3), (R0), (R2). C49 `FoldOdd`: (F4), (F5), (F6), `coker_act_XiOpZ`, `fold_odd_of`. C39 `FoldHalf.A4_odd`, C39b `FoldCube.O5_X`, `FoldGroup.XbarFam`, `FoldGroup.twoM`.
- C49b `ContZero`: (V1), (V2), (V3).
- C29 `Filt.T`; C32 `Families.ds`; C44 `Stability.length_ds_pos`.

## Definition (new)

Write `N := 2 ^ Dance.mCount ds` and `K := 2 ^ ds.length`.

- `Data0 (ds : List Bool) (α : ℕ) (M' : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ) : Prop :=`
  `∀ s s', (¬ Dset ds s' ⊆ Dset ds s → M' s s' = 0) ∧ (Dset ds s = ∅ → M' s s' = 0) ∧`
  `(Dset ds s' ⊆ Dset ds s → Dset ds s ≠ ∅ → M' s s' ≠ 0 ∧ ∃ n : ℕ, (n : ℤ) = (α : ℤ) * 2 ^ ds.length + Houses.cHatH (Ids ds) ds.length (2 ^ ds.length - 1) (α : ℤ) (Dset ds s) (Dset ds s') ∧ 2 ^ n ∣ M' s s' ∧ ¬ 2 ^ (n + 1) ∣ M' s s')`.

## Part G — the Smith form at `i = 0` is decided by the data

- **(G1) C15 (Z3), general form.** For `ds` with `1 ≤ ds.length`, `1 ≤ α`, `Ids ds ≠ ∅` and `M'` with `Data0 ds α M'`: there are `P Q : Matrix (Fin N) (Fin N) ℤ` with `Odd P.det`, `Odd Q.det`, `u : ℕ → ℤ` with every `u j` odd, and `E : ℕ → ℕ` with `(E j : ℤ) = (α : ℤ) * 2 ^ ds.length + yHatS ds α (N - 2 - j)` for `j < N - 1`, such that `P * M' * Q = diagonal (fun j => if (j : ℕ) < N - 1 then u j * 2 ^ E j else 0)`.
- **(G2)** For `1 ≤ ds.length` and `1 ≤ α`: `Data0 ds α (Windows.finalMatrix ℤ ds α 0)`.

## Part Z — truncation with one zero diagonal entry

- **(Z3)** Let `m N : ℕ`, `X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[2]`, `Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ` with `∃ R, ∀ i j, X i j − (Y i j : ℤ_[2]) = 2 ^ N * R i j`; `P Q` over `ℤ` with odd determinants; `u : ℕ → ℤ` with every `u j` odd; `E : ℕ → ℕ` with `E j < N` for `j < m`; `P * Y * Q = diagonal (fun j : Fin (m + 1) => if (j : ℕ) < m then u j * 2 ^ E j else 0)`; and `X.det = 0`. Then there are `P' Q'` over `ℤ_[2]` with unit determinants and `P' * X * Q' = diagonal (fun j : Fin (m + 1) => if (j : ℕ) < m then (2 : ℤ_[2]) ^ E j else 0)`.

## Part V — the Smith form of `Ξ_0` and its equivalence with `M^{(α)}(l, 0)`

Hypotheses (H0), as in C49b: `1 ≤ l`, `2 ≤ α`, `η : ℤ_[2]` with `IsUnit η`, `z : ℕ → ℤ_[2]`, and `GkZ` with `DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ`. Write `ds := Families.ds l`, `cs := Fin.cast (Smith2.slots_cast ds)` and `X := (finalM GkZ).submatrix cs cs`, a matrix on `Fin (2 ^ Dance.mCount ds)` over `ℤ_[2]`.

- **(V4) Truncations.** Under (H0) there is `N₀` such that for every `N ≥ N₀`: `Data0 ds α (Smith2.trunc N X)`; and every `E : ℕ → ℕ` with `(E j : ℤ) = (α : ℤ) * 2 ^ ds.length + yHatS ds α (2 ^ Dance.mCount ds - 2 - j)` for `j < 2 ^ Dance.mCount ds - 1` has `E j < N` for those `j`.
- **(V5) Smith form over `ℤ_[2]`.** Under (H0) and `Ids ds ≠ ∅`: there are `P Q` over `ℤ_[2]` with unit determinants and `E : ℕ → ℕ` with `(E j : ℤ) = (α : ℤ) * 2 ^ ds.length + yHatS ds α (2 ^ Dance.mCount ds - 2 - j)` for `j < 2 ^ Dance.mCount ds - 1`, such that `P * X * Q = diagonal (fun j => if (j : ℕ) < 2 ^ Dance.mCount ds - 1 then (2 : ℤ_[2]) ^ E j else 0)`.
- **(V6)** For `1 ≤ ds.length`, `1 ≤ α`, `Ids ds ≠ ∅`, the same holds for `(Windows.finalMatrix ℤ ds α 0).map (Int.castRingHom ℤ_[2])` in place of `X` (any `ds`, no dance needed).
- **(V7) Equivalence.** Under (H0) there are `P Q` over `ℤ_[2]` with unit determinants and `X = P * (Windows.finalMatrix ℤ ds α 0).map (Int.castRingHom ℤ_[2]) * Q`.

## Part R — the cokernel at `c = 0`, and Theorem 10.16

- **(R6)** For `1 ≤ l`, `2 ≤ α`, `IsUnit η`, `z : ℕ → ℤ_[2]` and every `B ≥ l + 1`: the cokernel of `FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m))` is isomorphic (`Nonempty (… ≃ₗ[ℤ_[2]] …)`) to `FamilyGroup.X (Families.ds l) α 0`. (No dance is assumed: C48b (T3) gives one.)
- **(R7) Theorem 10.16.** For every `l c : ℕ`, `2 ≤ α`, `IsUnit η`, `z : ℕ → ℤ_[2]` and `B ≥ l + 1`: the cokernel of `FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m))` is isomorphic to `FamilyGroup.X (Families.ds l) α c`.

## Part C — Corollary 10.17 for every index

- **(C4)** For every `l j : ℕ`: the cokernel of `FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1)` is isomorphic (`≃ₗ[ℤ_[2]]`) to the cokernel of `FoldCube.SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ))` (C49 (C1) without its hypothesis; parenthesise each quotient, as C49 (C1)).
- **(C5) Corollary 10.17.** For every `l j : ℕ`: `Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j))`.

## Proof sketch

- (G1): re-run C15 `Z_floor`, `Z_ceil`, `Z_main` for `Mo' := M'.submatrix (sl ds) (sl ds)` (positions in the o-order), exactly as C46 `G_floor`, `G_ceil`, `G_main` re-ran `S_floor`, `S_ceil`, `S_main`. The proofs of C15 use `Mo ds α 0` only through three facts, which `Data0` gives after `Dset ds (sl ds p) = dancer (Ids ds) p` (C15 `P1`):
  - `Mo_off`: off nested pairs the entry is `0`;
  - `Mo_row_zero`: the row of position `0` is `0` (`dancer _ 0 = ∅`);
  - `Z_val`: for `(p : ℕ) ≠ 0` (equivalently `dancer p ≠ ∅`, `dancer_eq_empty_iff`) and nested pairs, the entry is nonzero with `padicValInt = α 2^k + Potential.cHat (Ids ds) k (2^k − 1) α p q`, and `Potential.cHat … p q = Houses.cHatH … (dancer p) (dancer q)` by definition.
  Then transfer back along `slPerm` as C46 (G1) and C15 (Z3) (`submatrix_perm_eq`, `odd_det_permMatrix`).
- (G2): C15 `Mo_off`/`theorem_D_ii`, `final_row_zero` and `Z_val` read in the slot order through `P1` and `sl_sl` (as C46 (G2)); `padicValInt` gives the exponent `n` (`two_pow_padicValInt_dvd`, `not_two_pow_succ_dvd`).
- (Z3): put `D := diagonal (…)` and `Z := P.map ι * X * Q.map ι = D + 2^N • R'` with `R'` integral (`ι = Int.castRingHom ℤ_[2]`). In blocks `Fin (m + 1) = Fin m ⊕ Fin 1` (e.g. `Fin.castSucc`/`Fin.last`, or `finSumFinEquiv`), `Z = [[A, b], [c, d]]` with `A = D₀ + 2^N R₀₀`, `D₀ = diagonal (u j 2^{E j})`. Then `T := D₀⁻¹ 2^N R₀₀` has entries `u_j⁻¹ 2^{N − E_j} R` in `2 ℤ_[2]` (`E j < N`), so `1 + T` has `det ≡ 1 mod 2`, a unit, and `A = D₀ (1 + T)`. The vectors `A⁻¹ b = (1 + T)⁻¹ D₀⁻¹ 2^N b'` and `c A⁻¹ = 2^N c' (1 + T)⁻¹ D₀⁻¹` are integral. Row and column operations by `[[1, 0], [−c A⁻¹, 1]]` and `[[1, −A⁻¹ b], [0, 1]]` (determinant `1`) give `blockdiag(A, s)`, `s = d − c A⁻¹ b`. Since `det Z = det P · det X · det Q = 0` and `det A = det D₀ · det (1 + T) ≠ 0`, `s = 0`. Finally `A (1 + T)⁻¹ = D₀` and `diagonal (u j⁻¹) D₀ = diagonal (2^{E j})` (`u j` odd, a unit of `ℤ_[2]`). (Any proof is fine; this one avoids inverting `D`.)
- (V4): as C46 (V2). By C49b (V1), `‖X s s'‖ = ‖(finalMatrix ℤ ds α 0 s s' : ℤ_[2])‖`; with (G2), `X` has the support of `Data0` and, on nested pairs with `Dset s ≠ ∅`, `‖X s s'‖ = 2^{−n}`. Take `N₀` larger than every such `n` and every `α 2^k + yHatS ds α j` (`j < N − 1`, finitely many). Then C46 `Z0` gives the data for `trunc N X`.
- (V5): (V4) with `N := N₀`, (G1) for `trunc N₀ X`, `Z0` for the congruence `X ≡ trunc N₀ X`, `X.det = 0` from C49b (V3), and (Z3) with `m := 2 ^ Dance.mCount ds − 1` (reindex `Fin (m + 1) ≃ Fin (2 ^ Dance.mCount ds)` by `finCongr`; `N = 2^{mCount} ≥ 2` when `Ids ds ≠ ∅`).
- (V6): C15 (Z3) mapped to `ℤ_[2]` (odd determinants and odd `u j` become units); multiply by `diagonal (fun j => if j < N − 1 then (u j : ℤ_[2])⁻¹ else 1)`.
- (V7): if `Ids ds ≠ ∅`, C46 (Z2) with (V5) and (V6) (the same diagonal: the exponents are given by the same formula). If `Ids ds = ∅`, both matrices are `0` (C15 (Z1) and C49b (V2)); take `P = Q = 1`.
- (R6): as C46 (R4). C48b (T3) gives `GkZ`. Then:
  - C40d (Q1) with `h = 0` gives `coker ≅ (Π_a …) × coker (2^k • mulVecLin (finalM GkZ))`;
  - the first factor is `SC ds` by `Dance.pqCast` (as C46 (R4), `e0`);
  - reindexing along `finCongr (slots_cast ds)` turns `mulVecLin (finalM GkZ)` into `toLin' X`;
  - (V7) and the units `P`, `Q` give `coker (2^k • toLin' X) ≅ coker (2^k • toLin' (finalMatrix ℤ ds α 0).map ι)`. Left multiplication by an invertible matrix is an automorphism of the target carrying one range onto the other; right multiplication by an invertible matrix does not change the range.
  - finally `FamilyGroup.X_equiv_coker ds α 0` read backwards.
- (R7): `1 ≤ c`: C48b (R2). `c = 0`, `l = 0`: C48b (R0). `c = 0`, `1 ≤ l`: (R6).
- (C4): C49 (F4), (F5), (F6) as in C49 `coker_act_XiOpZ` and (C1), with (R7) in place of C48b (R2)/(R0): `PsiF j = XiOpZ 2 ⌈j/2⌉ (kJ j 1) (kJ j ·)` with `kJ j 1` a unit, and `SigF c = XiOpZ 2 c 1 0`.
- (C5): C39 `A4_odd`, (C4), C39b `O5_X` read backwards (as C49 `fold_odd_of`).

## Checks before formalization

`chkC49c.py` (md5 `b3480aaf55fc6a6d44e58a41e295fdfc`; exact rationals; the engines of `chkC15.py`: the dance of C13, slots, dancers, Smith exponents, PAVA).
- **(D):** for every `ds` of length `≤ 5` with `length + |I| ≤ 6` and `α = 1, 2, 3` (93 matrices), the integer final matrix at `i = 0` satisfies `Data0` (`cHatH = RH a − RH b + γ(a ∖ b)`, `RH` the ruler with `μ = 2^k − 1`). It has the Smith exponents of C15 (Z3), with one infinite exponent; when `I = ∅` it is `0`.
- **(G):** every entry multiplied by a random odd integer (three trials per matrix): `Data0` is kept and the Smith exponents are unchanged.
- **(Z):** `n = 2…5`, `N = 2…6`, 800 random cases `Z = D + 2^N R` with the corner chosen so that `det Z = 0` (the corner is then in `2^N ℤ_(2)`): the Smith exponents are the `E j` and one infinite exponent.
- Theorem 10.16 at `c = 0` and Corollary 10.17 at `j = 0` were measured in `chkC49b.py` (Smith forms of `Ξ_0` and `σ_0` on `T(l)`, `l = 1…9`) and `chkC49.py` (`coker Ψ_j ≅ coker Σ_c` on `T(l)` for `j = 0…5`).

Result: 2 437 checks, 0 failures.

Controls, five of five fire:
- the valuation `+1` (78 of 78 matrices with `I ≠ ∅` fail `Data0`);
- `μ = 2^k` in place of `2^k − 1` (78 of 78);
- one nested entry doubled changes the Smith form (138 cases);
- (Z) with some `E j = N` (140 cases);
- (Z) with `det Z ≠ 0` (800 cases: the last exponent becomes finite).
