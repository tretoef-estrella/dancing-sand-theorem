# C45 — Conjugation by `η^D` along the dance, invertibility, and Theorem 10.12 first half for every unit `η` (paper v8 §10.4)

*Lean piece C45 of the Dancing Sand Theorem. Grepy Escribano, 9 October 2026. Folder `RequestProject/Conjugation/`, namespace `Conjugation`. Do not change any earlier file.*

C44 proved Theorem 10.12, first half, for `η = 1`. The paper's proof of Theorem 10.12 uses `M_w(Σ) = η·M_w(F + η^{−1}π(D))` and «the proof of Theorem 4.4 uses only the products of the payment over windows». Here we take a cleaner route that needs no new window computation: **conjugation by `η^D`**. In the algebra `𝔅` of C40, conjugation by the diagonal operator `η^D` multiplies the coefficient of `F^{(m)}` by `η^m`; it turns `Ξ` with unit `η` into `Ξ'` with `η = 1` and `ζ'_m = η^{−m} ζ_m`, and it commutes with the dance up to explicit scalars. So the final matrix of `Ξ` is the final matrix of `Ξ'` with every entry multiplied by `η^{o(D_s) − o(D_{s'}) − (K − 1)}`, and C44 applies. We also remove the hypotheses «`Ξ`, `Σ` have two-sided inverses» and «the dance of `Σ` is clean»: both are proved here.

## Setting (reuse; do not redefine)

- C40 `FormalOps.Bf` (its ring structure, `coef`, the scalar action), `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`; C40b `FormalDance.Agree`, `MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `DanceRel`, `finalM`, `paySys`, `L4_sigma`, `L5`, `danceRel_unique`; C13 `Dance.slots`, `Dance.slots_eq`, `Dance.splitIso`, `Dance.mCount`; C3 `Rulers.oE`; C14 `Windows.Dset`, `Windows.Ids`; C32 `Families.ds`; C42 `InvFloors.slotOf` (if useful); C10 `Deficit.Mc`; C43 `PathSum.piF`, `XiOp`, `SigOp`, `instOddUnitsPadicTwo`; C44 `Stability.hadOne`, `Stability.F1`, `Stability.T1`, `Stability.T2`.

`A` is a commutative ring; `u, c : Aˣ` are units. Write `k := ds.length`, `K := 2^k`, `m := Dance.mCount ds`.

## Definitions (new)

- `cj (u : A) (x : Bf A) : Bf A` with `(cj u x).coef j f = u ^ j * x.coef j f` (conjugation by the diagonal operator `u^D`).
- `cjSys (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) : Matrix n n (Bf A)`, `cjSys c u w G s s' := ((c * w s * (w s')⁻¹ : Aˣ) : A) • cj u (G s s')`.

## Statements to prove

### Part C — conjugation commutes with the dance

- **(C1) `cj u` is a ring endomorphism.** `cj u 1 = 1`, `cj u (x + y) = cj u x + cj u y`, `cj u (x * y) = cj u x * cj u y`, `cj u (a • x) = a • cj u x`, `cj u (cj v x) = cj (u * v) x`, `cj 1 x = x`; and `Agree x y → Agree (cj u x) (cj u y)`. For systems over a `Fintype n` with `DecidableEq`: `cjSys 1 u w 1 = 1`, `cjSys c u w G * cjSys c' u w H = cjSys (c * c') u w (G * H)`, `cjSys c u w (G − H) = cjSys c u w G − cjSys c u w H`, `cjSys c u w (a • G) = a • cjSys c u w G`, and `MAgree G H → MAgree (cjSys c u w G) (cjSys c u w H)`.
- **(C2) The twist map and the V-split.** For every `G`:
  `twP (cjSys c u w G) = cjSys (c * u) (u ^ 2) w (twP G)`,  `twC (cjSys c u w G) = cjSys c (u ^ 2) w (twC G)`,
  `twB (cjSys c u w G) = cjSys c (u ^ 2) w (twB G)`,  `twD (cjSys c u w G) = cjSys (c * u⁻¹) (u ^ 2) w (twD G)`,
  `vsplit (cjSys c u w G) = cjSys c u (fun q => w q.1 * u ^ (q.2 : ℕ)) (vsplit G)`
  (exact equalities, or `MAgree` if that is what the definitions give; say which).
- **(C3) A clean move.** `CleanStep G G' → CleanStep (cjSys c u w G) (cjSys (c * u⁻¹) (u ^ 2) w G')`, and the same for a split move: `CleanStep (vsplit G) G'' → CleanStep (vsplit (cjSys c u w G)) (cjSys (c * u⁻¹) (u ^ 2) (fun q => w q.1 * u ^ (q.2 : ℕ)) G'')`.
- **(C4) The dance.** For every `ds`, `r`, `G : Matrix (Fin r) (Fin r) (Bf A)`, `Gk` with `DanceRel ds r G Gk`, and units `c`, `u`, `w : Fin r → Aˣ`:
  `DanceRel ds r (cjSys c u w G) (cjSys (c * u⁻¹ ^ (2 ^ k − 1)) (u ^ 2 ^ k) w_k Gk)`,
  where `w_k j := w (q j) * u ^ Rulers.oE (Windows.Dset ds j)` and `q j : Fin r` is the slot `⌊j / 2^m⌋` (a final slot `j` of the dance comes from the slot `⌊j / 2^m⌋` of the start; its dancers are `Windows.Dset ds j`). An equivalent recursive description of `w_k` is fine if it is proved equal to this one for `r = 1`.
- **(C5) The final matrix.** `finalM (cjSys c u w G) s s' = (c * w s * (w s')⁻¹ : A) * finalM G s s'`. Hence for `r = 1`, `w = 1`, `c = 1`: if `DanceRel ds 1 (fun _ _ => x) Gk` then there is `Gk'` with `DanceRel ds 1 (fun _ _ => cj u x) Gk'` and
  `finalM Gk' s s' = (u ^ Rulers.oE (Windows.Dset ds s) * (u⁻¹) ^ Rulers.oE (Windows.Dset ds s') * (u⁻¹) ^ (2 ^ k − 1) : A) * finalM Gk s s'`.

### Part D — agreement and the dance; invertibility

- **(D0)** `DanceRel ds r G Gk → MAgree G G' → DanceRel ds r G' Gk`.
- **(I)** Over a field `K`: if `x.coef 0 f ≠ 0` for every `f ≥ 0`, there is `Y : Bf K` with `Agree (x * Y) 1` and `Agree (Y * x) 1`.

### Part X — the operators

- **(X1)** For `η : ℚ_[2]`, `η ≠ 0`, and `ζ`: `PathSum.XiOp α c η ζ = cj η (PathSum.XiOp α c 1 (fun j f => η⁻¹ ^ j * ζ j f))` and `PathSum.SigOp α c η = cj η (PathSum.SigOp α c 1)`.
- **(X2)** If `‖η‖ = 1` and `‖ζ j f‖ ≤ 1` for `j ≥ 2`, then `‖η⁻¹ ^ j * ζ j f‖ ≤ 1`.

### Part T — Theorem 10.12, first half, for every unit `η`

Let `l ≥ 1`, `α ≥ 2`, `c ≥ 1`, `η : ℚ_[2]` with `‖η‖ = 1`, `ζ` with `‖ζ j f‖ ≤ 1` for `j ≥ 2`, and `GΞ` with `DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ` (the only hypothesis on the dance: the dance of `Ξ` is clean over `ℚ_2`). Then there is `GSig` with `DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c η) GSig` such that:

- **(T1η)** `IsUnit (finalM GΞ).det`, `IsUnit (finalM GSig).det`, and there is `E'` with `finalM GΞ = Stability.hadOne (finalM GSig) E'` and `‖E' s s'‖ ≤ 2^{−(α−1)}` for all `s, s'`;
- **(T2η)** for all `s, s'`: `finalM GΞ s s' = 0 ↔ finalM GSig s s' = 0` and `‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖`;
- **(F1η)** for all `s, s'`: `finalM GSig s s' = η ^ (o(D_s) − o(D_{s'}) − (K − 1) : ℤ) · Mc(D_s, D_{s'})` on nested pairs (`D_{s'} ⊆ D_s`) and `0` otherwise, with `Mc = Deficit.Mc (Windows.Ids ds) k α c` cast from `ℚ`, `D_s = Windows.Dset ds s`, `o = Rulers.oE`.

## Proof sketch

- (C1): entrywise from the product formula `(xy)_j(f) = Σ_a C(j, a) x_a(f) y_{j−a}(f − a)`: `u^a u^{j−a} = u^j`. Systems: `(c w_s w_t⁻¹)(c' w_t w_{s'}⁻¹) = c c' w_s w_{s'}⁻¹`.
- (C2): `tw10 x` at `(q, f)` is `dfi(q+1) x_{2q+1}(2f+1)`, so the coefficient `q` picks up `u^{2q+1} = u·(u²)^q`; `tw11`, `tw00` pick up `u^{2q} = (u²)^q`; `tw01` at `(q+1, f)` reads `x_{2q+1}(2f)` and picks up `u^{2q+1} = u⁻¹ (u²)^{q+1}`. `vplus x` at `(j, f)` is `x_j(f+1)` (factor `u^j`); `vprime x` at `(j, f)` is `x_{j+1}(f+1)` (factor `u·u^j`), which is the weight `u` on the `V`-slot `1`.
- (C3): with the witness `Q` of the move, take `Q' := cjSys (c * u)⁻¹ (u ^ 2) w Q`. Then `twP' Q' = cjSys 1 (u²) w (twP Q)` agrees with `1`, and `twD' − twB' Q' twC' = cjSys (c u⁻¹) (u²) w (twD − twB Q twC)`, which agrees with `2 · cjSys (c u⁻¹) (u²) w G'`. The split move is (C2) for `vsplit` followed by the twist case.
- (C4): induction on `ds` (as in C40d `FormalProp.Q1_aux`), for all `r`, `c`, `u`, `w`; the relabelling of a split move carries `w` along `Dance.splitIso`; the new dancer bit (the first split is the highest bit of `j mod 2^m`) adds `u^{2^h}` at level `h`, so `w_k` collects `u^{o(D_j)}`; the scalars `u⁻¹, u⁻², …` collect `u^{−(2^k − 1)}`.
- (C5): `cj u` does not change the coefficient `j = 0`.
- (D0): C40b (C3) (`MAgree` passes through the twist blocks and `vsplit`) and transitivity of `MAgree`, induction on `ds`.
- (I): the right inverse by the recursion of C43 (P0) (`Y_L(f) = ([L = 0] − Σ_{a ≥ 1} C(L, a) x_a(f) Y_{L−a}(f − a)) / x_0(f)` on `f ≥ L`); a left inverse `Z` by the mirror recursion; then `Z = Z(xY) = (Zx)Y = Y` up to agreement (C40b (C2)).
- (T): (X1) with `ζ'`; (C5) with `u = η⁻¹` turns `GΞ` into a dance of `Ξ' := XiOp α c 1 ζ'`; `L4_sigma` and (D0) give a dance of `Σ' := SigOp α c 1` (it agrees with `paySys (Dance.pσ α c) Dance.κσ`); (I) gives the two-sided inverses; C44 (T1), (T2), (F1) apply to `Ξ'`, `Σ'`; (C5) with `u = η` gives the dance `GSig` of `Σ = cj η Σ'` and both final matrices of the `η`-operators are the `η = 1` ones with the same diagonal unit factors (`L5` identifies `finalM GΞ` with the transported one); `hadOne (D₁ M D₂) E' = D₁ (hadOne M E') D₂` for diagonal `D₁, D₂`; and `‖η‖ = 1` keeps every norm.

## Checks done before sending
- Brute force `chkC45.py` (built on `chkC43.py`: formal operators as tables, the twist map `tw`, `vplus`, `vprime`, the lattice model of `T(l)`, exact rationals). Part C: 25 random operators and `u ∈ {±3, ±1, 5}/{1, 3, 5, 7}`: `cj` multiplicative, additive, invertible; the four twist identities and the two `V`-split identities. Part I: 25 random operators with non-zero `x_0`: the recursion gives a right inverse that is also a left inverse. Part X: the identity `XiOp η = cj η (XiOp 1 ζ')`, ten data. Parts C5 and T on `T(l)`: `l ≤ 7`, `α = 2, 3`, `c = 1, 3`, `η ∈ {3, −1, 1/3, −5/3}` (`1/3` is the unit of Theorem 10.16): `M_w(Ξ_η)_{ss'} = η^{o(D_s) − o(D_{s'}) − (K−1)} M_w(Ξ'_1)_{ss'}` and the same for `Σ`, entry by entry; `M_w(Ξ_η) = M_w(Σ_η) ∘ (1 + E')` with `v_2(E') ≥ α − 1`, the bound attained for `α = 2, 3`; the scaling is non-trivial in many entries. **1 391 checks, 0 failures.** `logs/chkC45.log`.
- Controls (all four fire): the exponent without `−(K − 1)`; the exponent with the opposite sign; `ζ' = ζ` without `η^{−m}`; `tw01` without the factor `u⁻¹`.

## Notes
- §10.4 is in six pieces: C41–C44 (certified or running), C45 (this piece), C46 (Theorem 10.12, second half: the Smith form of `M_w(Ξ)` over `ℤ_2` from its valuations and support (C15 Theorem 7.10 sees nothing else), and `coker(Ξ on T(l)) ≅ X^{(α)}(l, c)` through C40d Proposition 10.7; this needs the dance over `ℤ_2` and its image over `ℚ_2`).
- The route by conjugation replaces the paper's sentence «the proof of Theorem 4.4 uses only the products of the payment over windows» by a proved identity; the result is the same.
