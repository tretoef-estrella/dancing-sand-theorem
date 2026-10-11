# C44 — Lemma 10.11 (stability) and Theorem 10.12, first half (rigidity of the final matrix), for `η = 1` (paper v8 §10.4)

*Lean piece C44 of the Dancing Sand Theorem. Grepy Escribano, 9 October 2026. Folder `RequestProject/Stability/`, namespace `Stability`. Do not change any earlier file.*

C43 gave the relation of the final inverses: `M_w(Ξ)^{−1} = M_w(Σ)^{−1} ∘ (1 + E)` with `‖E‖ ≤ 2^{−(α−1)}` entrywise. This piece inverts it (Lemma 10.11) and proves the first half of Theorem 10.12: **`M_w(Ξ) = M_w(Σ) ∘ (1 + E')` with `‖E'‖ ≤ 2^{−(α−1)}` entrywise**, hence the same support and the same entry valuations. Here `η = 1`. The general unit `η`, the Smith form and the cokernel `X^{(α)}(l, c)` (the rest of Theorem 10.12) go to C45.

For matrices `B`, `E` of the same size, `B ∘ (1 + E)` is the matrix with entries `B_{ij}(1 + E_{ij})`; in Lean `hadOne B E := Matrix.of fun i j => B i j * (1 + E i j)`.

## Setting (reuse; do not redefine)

- C3 `Rulers.oE`, `Rulers.delta`; C10 `Deficit.a`, `Deficit.pi0`, `Deficit.Mc`, `Deficit.lemma_4_5`, `Deficit.lemma_4_5_empty`, `Deficit.A4_subadditivity`; C13 `Dance.slots`, `Dance.slots_eq`, `Dance.mCount`, `Dance.pσ`, `Dance.κσ`; C14 `Windows.Ids`, `Windows.Dset`, `Windows.theorem_4_4`, `Windows.H3_final_matrix` (and the injectivity of the dancers on `{0, …, 2^m − 1}`, C14 `Labels`); C32 `Families.ds`.
- C40 `FormalOps.Bf`; C40b `FormalDance.Agree`, `MAgree`, `DanceRel`, `finalM`, `paySys`, `L4_sigma`, `L5`, `danceRel_unique`; C42 `InvFloors.C109`; C43 `PathSum.piF`, `XiOp`, `SigOp`, `R`, `instOddUnitsPadicTwo`.

The field is `ℚ_[2]` with its norm (`‖x‖ ≤ 2^{−s}` means `v_2(x) ≥ s`). Write `ds := Families.ds l`, `k := ds.length`, `K := 2^k`, `ns := Dance.slots ds 1`, and for `s : Fin ns`, `D_s := Windows.Dset ds s`.

## Statements to prove

### Part S — the stability lemma, abstract (Lemma 10.11)

Let `n` be a `Fintype` with `DecidableEq`, `S : n → n → Prop` (`DecidableRel`) reflexive and transitive, and `ν : n → n → ℕ` with `ν i i = 0` and `ν i j ≤ ν i u + ν u j` whenever `S i u` and `S u j`.

**Definition.** `Wt S ν (s : ℕ) : Set (Matrix n n ℚ_[2]) := {X | ∀ i j, (¬ S i j → X i j = 0) ∧ ‖X i j‖ ≤ (2 : ℝ) ^ (−((ν i j + s : ℕ) : ℤ))}`.

- **(S0) The weighted ring.** `1 ∈ Wt S ν 0`; `Wt S ν s` is closed under `+`, negation, and multiplication by scalars `a` with `‖a‖ ≤ 1`; `X ∈ Wt S ν s`, `Y ∈ Wt S ν t` imply `X * Y ∈ Wt S ν (s + t)`; `Wt S ν (s + 1) ⊆ Wt S ν s`.
- **(S1) Stability.** Let `s ≥ 1`, `A ∈ Wt S ν 0` with `‖A i j‖ = 2^{−ν i j}` whenever `S i j`, `B ∈ Wt S ν 0` with `A * B = 1`, and `E` with `‖E i j‖ ≤ 2^{−s}` for all `i, j`. Then `IsUnit (hadOne B E).det`, and there is `E'` with `(hadOne B E)⁻¹ = hadOne A E'` and `‖E' i j‖ ≤ 2^{−s}` for all `i, j`.
- **(S2) With diagonal scalings.** In the setting of (S1), let `d₁ d₂ : n → ℚ_[2]` with all values non-zero and `M := diagonal d₁ * A * diagonal d₂`. Then `IsUnit M.det`, `IsUnit (hadOne M⁻¹ E).det`, and there is `E'` with `(hadOne M⁻¹ E)⁻¹ = hadOne M E'` and `‖E' i j‖ ≤ 2^{−s}` for all `i, j`.

(The paper's Lemma 10.11 is (S2) with `s = 1`; here `s` is general, so the bound `α − 1` of C43 passes through unchanged.)

### Part A — the matrix `𝒜` of the word

For `ds : List Bool` with `k := ds.length ≥ 1`, on `Fin (Dance.slots ds 1)`:
- `nest ds s s' : Prop := Windows.Dset ds s' ⊆ Windows.Dset ds s`;
- `Amat ds s s' : ℚ_[2] := if nest ds s s' then (Deficit.a (Windows.Ids ds) k (D_s \ D_{s'}) : ℚ_[2]) else 0`;
- `nuA ds s s' : ℕ := (Rulers.delta k (D_s \ D_{s'})).toNat`.

- **(A1)** `s ↦ D_s` is injective on `Fin (Dance.slots ds 1)`; `nest ds` is reflexive and transitive; `nuA ds s s = 0`; and `nuA ds s t ≤ nuA ds s u + nuA ds u t` whenever `nest ds s u` and `nest ds u t`. (Also `Rulers.delta k Δ ≥ 0` for `Δ ⊆ Ids ds`, so `toNat` loses nothing.)
- **(A2)** `nest ds s s' → ‖Amat ds s s'‖ = 2 ^ (−(nuA ds s s' : ℤ))`; `Amat ds s s = 1`.
- **(A3)** `Amat ds ∈ Wt (nest ds) (nuA ds) 0`, and there is `B ∈ Wt (nest ds) (nuA ds) 0` with `Amat ds * B = 1`.

### Part F — the final matrix of `Σ` (`η = 1`)

Let `l ≥ 1`, `α ≥ 1`, `c ≥ 1`, and `GSig` with `DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c 1) GSig`.

- **(F1) `M_w(Σ)` is the closed form.** For all `s s'`: `finalM GSig s s' = if nest ds s s' then ((Deficit.Mc (Windows.Ids ds) k (α : ℤ) c D_s D_{s'} : ℚ) : ℚ_[2]) else 0`.
- **(F2) The factorization `M_w(Σ) = 𝔡₁ 𝒜 𝔡₂`.** With
  `d₁ s := −2^{1 − K} · 2^{o(D_s)} / ∏_{d ∈ range (o(D_s))} pi0 α c d` and `d₂ s := 2^{−o(D_s)} · ∏_{d ∈ range (o(D_s) + K)} pi0 α c d`
  (in `ℚ`, cast to `ℚ_[2]`; `o = Rulers.oE`): `finalM GSig = diagonal d₁ * Amat ds * diagonal d₂`, and `d₁ s ≠ 0`, `d₂ s ≠ 0` for every `s`.

### Part T — Theorem 10.12, first half (`η = 1`)

Let `l ≥ 1`, `α ≥ 2`, `c ≥ 1`, `ζ` with `‖ζ m f‖ ≤ 1` for `m ≥ 2`, `B ≥ l + 1`, `YΞ YSig : Bf ℚ_[2]` two-sided inverses (in the sense of `Agree`) of `XiOp α c 1 ζ` and `SigOp α c 1`, and `GΞ`, `GSig` with `DanceRel (Families.ds l) 1 (fun _ _ => XiOp α c 1 ζ) GΞ`, `DanceRel (Families.ds l) 1 (fun _ _ => SigOp α c 1) GSig` (the hypotheses of C43 (R) with `η = 1`).

- **(T1) Rigidity.** `IsUnit (finalM GΞ).det`, `IsUnit (finalM GSig).det`, and there is `E'` with `finalM GΞ = hadOne (finalM GSig) E'` and `‖E' s s'‖ ≤ 2^{−(α−1)}` for all `s, s'`.
- **(T2) Same support, same valuations.** For all `s, s'`: `finalM GΞ s s' = 0 ↔ finalM GSig s s' = 0`, and `‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖`.

## Proof sketch

- (S0): entrywise, by the ultrametric inequality; for the product, `(XY)_{ij} = Σ_u X_{iu} Y_{uj}` and a term is non-zero only if `S i u` and `S u j`, so `S i j` by transitivity and `ν i u + ν u j ≥ ν i j`.
- (S1): `A * B = 1` gives `B * A = 1`. Then `hadOne B E = B + B ⊙ E = B (1 + N)` with `N := A (B ⊙ E) ∈ Wt s` (by (S0); `B ⊙ E ∈ Wt s`). Every entry of `N` has norm `≤ 1/2`, so `‖det(1 + N) − 1‖ ≤ 1/2` (Leibniz: every permutation other than the identity meets an entry of `N`, and the identity term is `∏(1 + N_{ii})`), hence `det(1 + N)` is a unit. By Cayley–Hamilton, `(1 + N)^{−1}` is a polynomial in `1 + N` with coefficients of norm `≤ 1` (the characteristic polynomial of `1 + N` has coefficients of norm `≤ 1` and a unit constant term), so `(1 + N)^{−1} ∈ Wt 0`, and `(1 + N)^{−1} = 1 − N (1 + N)^{−1} ∈ 1 + Wt s`. So `(hadOne B E)^{−1} = (1 + N)^{−1} A ∈ A + Wt s`. Where `S i j`, put `E'_{ij} := ((hadOne B E)^{−1}_{ij} − A_{ij}) / A_{ij}` (norm `≤ 2^{−ν−s} / 2^{−ν}`); elsewhere both sides are `0` and `E'_{ij} := 0`. (A nilpotent or Neumann-series argument is equally fine.)
- (S2): `M^{−1} = diagonal d₂^{−1} * B * diagonal d₁^{−1}`, and `diagonal x * (hadOne Y E) * diagonal y = hadOne (diagonal x * Y * diagonal y) E` (diagonal scalings commute with `∘`); apply (S1).
- (A1): the dancers of a slot `s < 2^m` are a bijection onto the subsets of `I(ds)` (C14); `δ ≥ 0` because `Δ ⊆ [min Δ, k)`; subadditivity from `Deficit.A4_subadditivity` (strict for non-empty parts; with an empty part it is an equality), applied to `D_s ∖ D_t = (D_s ∖ D_u) ⊔ (D_u ∖ D_t)`.
- (A2): `Deficit.lemma_4_5` (`a_k(Δ) ≠ 0`, `v_2 = δ(Δ)`), `lemma_4_5_empty`; an integer `z` has `‖(z : ℚ_[2])‖ = 2^{−v_2(z)}`.
- (A3): `Amat = 1 − N` with `N` supported on strict nestings, `N ∈ Wt 0`; strict nestings have strictly decreasing cardinality, so `N^{m+1} = 0`; take `B := Σ_{j ≤ m} N^j` and use (S0).
- (F1): `SigOp α c 1` agrees with the payment system `paySys (Dance.pσ α c) Dance.κσ` at `r = 1` (both are `F + 2^α(D + c)` on the floors `f ≥ 0`; `2 · 2^{α−1} = 2^α` for `α ≥ 1`); `danceRel_unique` with the witness of `L4_sigma` gives `finalM GSig = Mfin (dance …)` over `ℚ_[2]`; `H3_final_matrix` moves it to `ℤ` and back to `ℚ`, where `theorem_4_4` identifies it with `Mc` (`Fin.cast` along `slots_eq`).
- (F2): for `D' ⊆ D`, `o(D ∖ D') = o(D) − o(D')` and `∏_{[o_D, o_{D'}+K)} = ∏_{range(o_{D'}+K)} / ∏_{range(o_D)}`; `pi0 α c d ≠ 0` for `c ≥ 1`; off the nesting both sides are `0`.
- (T1): C43 `R` gives `(finalM GΞ)⁻¹ = hadOne (finalM GSig)⁻¹ E` with `‖E‖ ≤ 2^{−(α−1)}` (choose `E_{ss'} := 0` where the `Σ` entry is `0`); C42 `C109` gives both `IsUnit det`; then (S2) with `A := Amat ds`, (A1)–(A3), (F2) and `s := α − 1 ≥ 1`, and `(M⁻¹)⁻¹ = M`.
- (T2): `‖1 + e‖ = 1` when `‖e‖ < 1`.

## Checks done before sending
- Brute force `chkC44.py` (built on `chkC43.py`: independent lattice model of `T(l)`, exact rationals; the final matrices computed as the inverses of `2^k O G^{−1} I`, C41 (V5)). Part A: every `l ≤ 63` — the dancers injective, `𝒜_{ss} = 1`, `v_2(𝒜_{ss'}) = δ(D_s ∖ D_{s'})` exactly on nested pairs, `𝒜^{−1}` zero off the nesting and `v_2 ≥ δ` on it, subadditivity on every nested triple. Part F: `l ≤ 7`, `α = 2, 3`, `c = 1, 2, 3`: `M_w(Σ) = Mc` entrywise and `= 𝔡₁ 𝒜 𝔡₂`. Part T: the same cells, three random `ζ` each (integers in `[−6, 6]`): same support and `v_2(E') ≥ α − 1`, the bound attained for `α = 2, 3`, and `M_w(Ξ) ≠ M_w(Σ)` in some cells. Part S: 300 random weighted matrices (`ν = δ` on subsets, `s = 1, 2, 3`), with and without diagonal scalings. **11 994 checks, 0 failures.** `logs/chkC44.log`.
- Controls (all five fire): `E` with `v_2 = 0` allowed (stability fails); `𝔡₁` without `2^{o(D)}`; the bound `α` instead of `α − 1` in (T1); `η = 3` (then `M_w(Σ) ≠ Mc`: the restriction `η = 1` is real, and C45 handles it); the nesting is not total (the support claims are not vacuous).
- Two errors of my first run, both in the test, not in the statements: the memo of the coefficients `a_k` was rebuilt at every call (slow, not wrong), and two helper functions of `chkC43.py` lived after the cut I imported; repaired before the run that counts.

## Notes
- The bound in (T1) is `2^{−(α−1)}`, stronger than the paper's `v_2(E') ≥ 1`; the paper's statement is the case `α = 2` and is implied for every `α ≥ 2`.
- §10.4 is in five pieces: C41, C42, C43 (certified or running), C44 (this piece), C45 (general unit `η`, the Smith form and the cokernel, the rest of Theorem 10.12).
