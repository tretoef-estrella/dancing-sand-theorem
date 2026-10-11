# Theorem 10.12, second half: the Smith form over ℤ_2 and the cokernel (paper v8 §10.4)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §10.4, Theorem 10.12: «Consequently `M_w(Ξ)` and `M_w(Σ)` have the same support and the same entry valuations, the same Smith form, and `coker(Ξ on T(l)) ≅ coker(Σ on T(l)) ≅ X^{(α)}(l, c)`», with the proof: «The Smith form of `M^{(α)}(l, c)` is computed in Theorems 6.5 and 7.10 from the valuations of its entries and from its support alone … all three matrices have the same Smith form. Proposition 10.7 gives the cokernels.»

Pieces C43–C45 proved the first half over `ℚ_2`: for a clean dance `GΞ` of `Ξ = XiOp α c η ζ`, there is a dance `GSig` of `Σ = SigOp α c η` with `finalM GΞ = hadOne (finalM GSig) E'`, `‖E'‖ ≤ 2^{−(α−1)}`, the same zeros and the same norms (`Conjugation.T_eta`). This piece does the second half: the dance of `Ξ` lives over `ℤ_2` (that is the hypothesis «the dance of `Ξ` is clean»), its final matrix has the Smith form of the dance matrix of `σ` (Theorem 7.10, piece C15), and its cokernel on `T(l)` is the family group `X^{(α)}(l, c)` (piece C16).

Folder `RequestProject/Smith2/`, namespace `Smith2`. Nothing of the project is redefined.

## Setting (reused, without changing them)

- C40 `FormalOps.Bf` (`x.coef m f`), its ring and algebra structure, `Bf.fd`, `Bf.dg`, `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`; C20 `Doubling.dfi`, `Doubling.OddUnits` (instances for `ℤ_[2]`, and `PathSum.instOddUnitsPadicTwo` for `ℚ_[2]`).
- C40b `FormalDance.Agree`, `MAgree`, `paySys`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `DanceRel`, `finalM`, `L4_sigma`, `L5`.
- C40c/C40d `FormalAct.sysAct`, `FormalProp.T`, `FormalProp.Q1`, `FormalProp.Q3`, `FormalProp.Q4`.
- C43 `PathSum.XiOp`, `PathSum.SigOp`, `PathSum.piF`; C44 `Stability.hadOne`, `Stability.nest`, `Stability.F1_gen`; C45 `Conjugation.T_eta`, `Conjugation.F1eta_gen`.
- C13 `Dance.slots`, `Dance.slots_eq`, `Dance.mCount`, `Dance.pσ`, `Dance.κσ`, `Dance.dance`, `Dance.Mfin`, `Dance.SysT`, `Dance.sigma`, `Dance.proposition_4_3`; C14 `Windows.Dset`, `Windows.Ids`, `Windows.finalMatrix`, `Windows.finalMatrix_eq_map`, `Windows.H3_final_matrix`, `Windows.theorem_D_ii`, `Windows.theorem_D_iii`; C10 `Deficit.Mc`; C32 `Families.ds`.
- C15 `DanceSmith` (`sl`, `slPerm`, `P1`, `Mo`, `S1`, `floor_minor`, `golden_ceiling`, `smith_of_bounds`, `S_floor`, `S_ceil`, `S_main`, `S3`, `Cst`, `yHat`, `xClk`); C4 `GoldenMatching.cHat`; C16 `FamilyGroup.X`, `FamilyGroup.SC`, `FamilyGroup.Q`, `FamilyGroup.X1`.

Write `ds := Families.ds l`, `k := ds.length`, `m := Dance.mCount ds`, `N := 2^m`, `I := Windows.Ids ds`, and `cs : Fin (2^m) ≃ Fin (Dance.slots ds 1)` for the cast along `Dance.slots_eq ds 1` and `one_mul` (the reindexing used in `L4_sigma` and `Windows.finalMatrix`). Norms are the norms of `ℤ_[2]` and `ℚ_[2]`.

## Definitions (new)

1. `Bf.map (φ : A →+* A') (x : Bf A) : Bf A'`, `(Bf.map φ x).coef m f = φ (x.coef m f)`.
2. `XiOpZ (α c : ℕ) (η : ℤ_[2]) (ζ : ℕ → ℤ → ℤ_[2]) : Bf ℤ_[2]` with `coef 0 f = 2 ^ α * ((f : ℤ_[2]) + c)`, `coef 1 f = η`, `coef j f = ζ j f` for `j ≥ 2` (the operator `Ξ` with integral data).
3. `trunc (N : ℕ) (X : Matrix n n ℤ_[2]) : Matrix n n ℤ`, `trunc N X i j = ((X i j).appr N : ℤ)` (`PadicInt.appr`).

## Part M — the formal dance along a ring homomorphism

Let `φ : A →+* A'` be a homomorphism of commutative rings.

- **(M1)** `Bf.map φ` is a ring homomorphism `Bf A →+* Bf A'`; `Bf.map φ (a • x) = φ a • Bf.map φ x`; `Bf.map φ (Bf.fd m) = Bf.fd m`; `Bf.map φ (Bf.dg p) = Bf.dg (φ ∘ p)`.
- **(M2)** If `[OddUnits A]` (so that `φ (dfi s) = dfi s`): `Bf.map φ` commutes with `tw00`, `tw11`, `tw10`, `tw01`; and with `vplus`, `vprime` (no hypothesis).
- **(M3)** `Agree x y → Agree (Bf.map φ x) (Bf.map φ y)`; for matrices, with `G.map (Bf.map φ)`: products and sums commute with the map, `MAgree` is preserved, and `twP`, `twC`, `twB`, `twD`, `vsplit` commute with the map; `((2 : A) • G).map (Bf.map φ) = (2 : A') • G.map (Bf.map φ)`.
- **(M4)** If `[OddUnits A]`: `CleanStep G G' → CleanStep (G.map (Bf.map φ)) (G'.map (Bf.map φ))`; `DanceRel ds r G Gk → DanceRel ds r (G.map (Bf.map φ)) (Gk.map (Bf.map φ))`; and `finalM (Gk.map (Bf.map φ)) = (finalM Gk).map φ`.
- **(M5)** With `ι : ℤ_[2] →+* ℚ_[2]` the coercion: `Bf.map ι (XiOpZ α c η ζ) = PathSum.XiOp α c (η : ℚ_[2]) (fun j f => (ζ j f : ℚ_[2]))`, and `(paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ).map (Bf.map ι) = paySys (Dance.pσ (A := ℚ_[2]) α c) Dance.κσ`.

## Part Z — the Smith form over ℤ_2 by truncation

- **(Z0)** For `x : ℤ_[2]` and `N`: `x − ((x.appr N : ℕ) : ℤ_[2]) ∈ (2 : ℤ_[2]) ^ N • ⊤` (i.e. `= 2^N * r` for some `r`); if `x = 0` then `x.appr N = 0`; if `x ≠ 0`, `‖x‖ = 2^{−n}` and `n < N`, then `y := ((x.appr N : ℕ) : ℤ)` satisfies `y ≠ 0`, `2^n ∣ y` and `¬ 2^(n+1) ∣ y`.
- **(Z1)** Let `X : Matrix (Fin n) (Fin n) ℤ_[2]`, `Y : Matrix (Fin n) (Fin n) ℤ`, `N : ℕ` with `X i j − (Y i j : ℤ_[2]) = 2^N * R i j` for some `R`. Suppose `P Q : Matrix (Fin n) (Fin n) ℤ` with `Odd P.det`, `Odd Q.det`, odd integers `u j`, and `E : ℕ → ℕ` with `E j < N` for `j < n`, such that `P * Y * Q = diagonal (fun j => u j * 2 ^ E j)`. Then there are `P' Q' : Matrix (Fin n) (Fin n) ℤ_[2]` with `IsUnit P'.det`, `IsUnit Q'.det` and `P' * X * Q' = diagonal (fun j => (2 : ℤ_[2]) ^ E j)`.
- **(Z2)** If `P₁ * X₁ * Q₁ = D` and `P₂ * X₂ * Q₂ = D` with all four determinants units, then `X₂ = P * X₁ * Q` for some `P, Q` with unit determinant.

## Part G — the Smith form is decided by the support and the entry valuations (C15 (S3), general form)

- **(G1)** Let `ds` with `1 ≤ ds.length`, `1 ≤ α`, `1 ≤ i`, and `M' : Matrix (Fin (2^m)) (Fin (2^m)) ℤ` such that for all `s, s'`:
  - if `¬ Windows.Dset ds s' ⊆ Windows.Dset ds s` then `M' s s' = 0`;
  - if `Windows.Dset ds s' ⊆ Windows.Dset ds s` then `M' s s' ≠ 0` and there is `n : ℕ` with `(n : ℤ) = DanceSmith.Cst ds α i + GoldenMatching.cHat k I α (i − 1) (Windows.Dset ds s) (Windows.Dset ds s')`, `2^n ∣ M' s s'`, `¬ 2^(n+1) ∣ M' s s'`.

  Then the conclusion of `DanceSmith.S3` holds for `M'`: there are `P, Q` over `ℤ` with odd determinants, odd integers `u j` and `E : ℕ → ℕ` with `(E j : ℤ) = Cst ds α i + yHat ds α i (N − 1 − j)` for `j < N`, and `P * M' * Q = diagonal (fun j => u j * 2 ^ E j)`.
- **(G2)** `Windows.finalMatrix ℤ ds α i` satisfies the hypothesis of (G1) (for `1 ≤ ds.length`, `1 ≤ α`, `1 ≤ i`).

## Part V — the entries of M_w(Ξ) over ℤ_2

Hypotheses (H): `1 ≤ l`, `2 ≤ α`, `1 ≤ c`, `η : ℤ_[2]` with `IsUnit η`, `ζ : ℕ → ℤ → ℤ_[2]`, and `GkZ : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf ℤ_[2])` with `DanceRel ds 1 (fun _ _ => XiOpZ α c η ζ) GkZ` (the dance of `Ξ` is clean over `ℤ_2`). Write `X s s' := finalM GkZ (cs s) (cs s')` for `s s' : Fin (2^m)`.

- **(V1)** Under (H), for all `s, s'`: `X s s' = 0 ↔ ¬ Windows.Dset ds s' ⊆ Windows.Dset ds s`, and if `Windows.Dset ds s' ⊆ Windows.Dset ds s` then `‖X s s'‖ = ‖((Windows.finalMatrix ℤ ds α c s s' : ℤ) : ℤ_[2])‖`.
- **(V2)** Under (H), there is `N₀` such that for every `N ≥ N₀`, `trunc N X` satisfies the hypothesis of (G1) with `i := c`, and `E j < N` for the exponents of (G1) (`j < 2^m`).

## Part R — Theorem 10.12, second half

Under (H):

- **(R1)** For every `GkS` with `DanceRel ds 1 (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ) GkS` there are `P Q : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) ℤ_[2]` with `IsUnit P.det`, `IsUnit Q.det` and `finalM GkZ = P * finalM GkS * Q`.
- **(R2)** (Smith form) There are `P, Q` over `ℤ_[2]` with unit determinants and `E : ℕ → ℕ` with `(E j : ℤ) = DanceSmith.Cst ds α c + DanceSmith.yHat ds α c (N − 1 − j)` for `j < N`, such that `P * finalM GkZ * Q = diagonal (fun j : Fin (Dance.slots ds 1) => (2 : ℤ_[2]) ^ E j)`.
- **(R3)** For every `B ≥ l + 1` and every `h`: `Nonempty` of a `ℤ_[2]`-linear equivalence between the cokernel of `(2 : ℤ_[2]) ^ h • sysAct (T ℤ_[2] l) l B (fun _ _ => XiOpZ α c η ζ)` and the cokernel of `(2 : ℤ_[2]) ^ h • sysAct (T ℤ_[2] l) l B (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ)` (both on `Fin 1 → (T ℤ_[2] l).ι → ℤ_[2]`). («`coker Ξ ≅ coker Σ`».)
- **(R4)** For every `B ≥ l + 1` there is `E : ℕ → ℕ` with `(E p : ℤ) = k + DanceSmith.Cst ds α c + DanceSmith.yHat ds α c p` for `p < N`, and `Nonempty` of an equivalence between the cokernel of `sysAct (T ℤ_[2] l) l B (fun _ _ => XiOpZ α c η ζ)` and `FamilyGroup.SC ds × ((p : Fin (2 ^ m)) → FamilyGroup.Q (E p))`.
- **(R5)** For every `B ≥ l + 1`: `Nonempty` of an equivalence between the cokernel of `sysAct (T ℤ_[2] l) l B (fun _ _ => XiOpZ α c η ζ)` and `FamilyGroup.X ds α c`. («`coker(Ξ on T(l)) ≅ X^{(α)}(l, c)`».)

## Proof sketch

- (M): coefficientwise; the product formula `(xy)_j(f) = Σ_a C(j, a) x_a(f) y_{j−a}(f − a)` uses only ring operations and natural casts; `dfi s = Ring.inverse ((2s−1)!!)` and `(2s−1)!!` is a unit of `A` (OddUnits), so `φ (Ring.inverse u) = Ring.inverse (φ u)`. (M4) by induction on `ds` as in C40b, the witness `Q` of each move mapped. (M5) coefficientwise (`PathSum.piF α c d = 2^α (d + c)`; `2 · pσ α c = 2^α (c + f)`).
- (Z0): `PadicInt.appr_spec`; the ultrametric inequality (`‖x − y‖ ≤ 2^{−N} < ‖x‖`) gives `‖(y : ℤ_[2])‖ = ‖x‖`, and the norm of an integer in `ℤ_[2]` is `2^{−v_2}`. (Z1): `P X Q = D + 2^N P R Q` with `D` the diagonal of `u j 2^{E j}`; `2^N P R Q = D · W` with `W i j = u_i⁻¹ 2^{N − E i} (P R Q) i j ∈ 2ℤ_[2]` (since `E i < N`), so `P X Q = D (1 + W)` and `det (1 + W) ≡ 1 (mod 2)` is a unit; the odd `u j` and the odd determinants of `P`, `Q` are units of `ℤ_[2]`. (Z2): algebra.
- (G1): the proof of C15 (S3) uses `Mo` only through its entries: re-run it with `Mo' := M'.submatrix sl sl` (`DanceSmith.P1`: `Dset ds (sl p) = dancer I p`), the floor `floor_minor` (tropical bound), the ceiling `golden_ceiling` (unique golden matching), and `smith_of_bounds`; then transfer back along `slPerm` as in `smith_transfer`. (G2): `DanceSmith.S1` with `P1`.
- (V1): map `GkZ` to `ℚ_2` (M4, M5); apply `Conjugation.T_eta`: zeros and norms of `finalM` agree with those of `finalM GSig`; by `F1eta_gen`, `finalM GSig = η^{z} · Mc` on nested pairs and `0` elsewhere, with `‖η‖ = 1`; by `Windows.theorem_D_ii`, `Mc` is the cast of `Windows.finalMatrix ℤ ds α c` on nested pairs. `Windows.theorem_D_iii` (with `0 < c + o_D`) shows that entry is non-zero. The coercion `ℤ_[2] → ℚ_[2]` preserves norms. (V2): (Z0), (V1), (G2), taking `N₀` above every entry exponent `n` and every `E j`.
- (R2): (V2), (G1) for `trunc N X`, (Z1). (R1): `finalM GkS` is the image of `Windows.finalMatrix ℤ ds α c` (L4_sigma over `ℤ_[2]`, `L5`, `finalMatrix_eq_map`), whose Smith form is `DanceSmith.S3` (odd integers become units); (Z2). (R3): `FormalProp.Q3` with (R1). (R4): `FormalProp.Q1` with `h = 0` for `Ξ`, then (R2) for the factor `coker (2^k · finalM GkZ)`, with the casts `1 * 2^…` and `0 + a` as in C16, and the reversal `p ↦ N − 1 − p`. (R5): (R4) and `FamilyGroup.X1` (same `E`).

## Checks before formalization

`chkC46.py` (exact rationals, the lattice model of `chkC43.py`, `T(l)` for `1 ≤ l ≤ 7`, `α ∈ {2, 3}`, `c ∈ {1, 3}`, `η ∈ {3, −1, 5/3, −7/5}`, random integral `ζ`; 112 cells): `M_w(Ξ)` integral at 2; the same zeros and entry valuations as the dance matrix of `σ`; the same Smith exponents at 2 for `M_w(Ξ)`, `M_w(Σ_η)` and the dance matrix of `σ`; the truncation keeps zeros and valuations and has the same Smith exponents; any `X = Y + 2^N R` has the Smith form of `Y` (Z1); and (G): every integer matrix with the support and the entry valuations of the dance matrix of `σ` (entries multiplied by random 2-adic units) has its Smith exponents. 1 008 checks, 0 failures. Controls, all four fire: truncation at `N = 1`; one entry valuation changed by one; one entry killed (`E' = −1`, which the bound `v_2(E') ≥ 1` excludes); `ζ` of valuation `−1`.
