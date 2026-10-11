# The dance modulo 2 (paper v8 §10.7, Lemma 10.18)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §10.7, Lemma 10.18.

§10.7 proves the fold law on the even families. Both sides of an even family are glued systems of size `2` whose two arms are odd-family operators (C39 A4_even, C39b V6). C50 proved that gluing commutes with the formal dance, provided the two arms are congruent modulo `2` at every level of their dances (`GlueDance.PairRel`). This piece supplies that hypothesis.

**Lemma 10.18.** Two good covariant systems (C48 `Good`) whose coefficient functions are congruent modulo `2` have dances that stay congruent modulo `2` at every level.

The difficulty is the twist move. In general a congruence modulo `2` of two systems gives only a congruence modulo `1` of the next levels (C49b K6 loses one power of `2`). Lemma 10.18 needs the structure of good systems:
- every value of a function of the class `𝒦` is congruent modulo `4` to its constant term (C47 K6);
- so modulo `4` the noncommutative product `prodFun` of C47 becomes the product of a commutative ring;
- in that ring the Schur complement is `D − β Q β`, with `Q` the inverse of the pivot;
- passing from one system to the other changes `β` by `2δ`, `Q` by `2·(…)`, and `D` by a multiple of `4`;
- so the Schur complement changes by `β²·2·(…)` modulo `4`;
- `β²` is even, because in this ring the square of an element is even except at the constant term, and the constant term of `β` is a payment, which is `≡ 0 (mod 4)`.

Folder `RequestProject/DanceMod2/`, namespace `DanceMod2`. Nothing of the project is redefined.

## Setting (reused, without changing them)

- C40 `FormalOps`: `Bf`. C40b `FormalDance`: `Agree`, `MAgree`, `vsplit`, `CleanStep`, `DanceRel`.
- C13 `Dance`: `slots`, `splitIso`. C49b `ContZero`: `MCong`.
- C47 `RingK`: `KRep`, `Kr`, `oS`, `Dn`, `covSys`, `prodFun`, (K6), (T2), and the proof of (R1)–(R2) (`RingK/PartR.lean`), to be copied for a general coefficient ring.
- C48 `Cleanliness`: `InK`, `PayA`, `CoefB`, `Good`, `GB`, `GC`, `GP`, `GD`, `vsplitG`, `splitDn`, `rinv`, `schurG`, (W2), (W3), `W4_strong`, (W5), (V1), (V2), (V3), `L1`, `GP_hyp`, `rinv_empty_zero`, `prodFun_rinv`.
- C48b `DanceXi`: (T1), (T2) (the model for Part D).
- C50 `GlueDance`: `glueC`, `PairRel`, (S4), (D1), (D2).
- Mathlib: `PadicInt.toZModPow`.

Throughout, `A := ℤ_[2]`.

## Definitions (new)

- `RA (R : Type*) := Finset ℕ → ℕ → R`, with pointwise addition and, for a commutative ring `R`:
  - `one : RA R := fun Δ q => if Δ = ∅ ∧ q = 0 then 1 else 0`;
  - `mul (β γ : RA R) : RA R := fun Δ q => ∑ Δ₁ ∈ Δ.powerset, ∑ a ∈ range (q + 1), (Nat.choose q a : R) * β Δ₁ a * γ (Δ \ Δ₁) (q - a)`.
  (This is C47 `RS` with the coefficient ring `R` in place of `𝒮`.)
- `red4 : ℤ_[2] →+* ZMod (2 ^ 2) := PadicInt.toZModPow 2`.
- `kap (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : RA (ZMod (2 ^ 2)) := fun Δ m => red4 (Γ Δ m 0)`.
- `Cong2 (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Prop := ∀ Δ m y, ∃ z, Γ Δ m y - Γ'' Δ m y = 2 * z`.

## Part R — the ring `RA R`

For every commutative ring `R`:

- **(R1)** `RA R` with `one` and `mul` is a commutative ring (an instance `RA.instCommRing`), with `(β * γ) Δ q` given by the formula of `mul` (`RA.mul_apply`) and `(1 : RA R) Δ q` by the formula of `one` (`RA.one_apply`). Copy C47 R1 (`RingK/PartR.lean`); nothing in that proof uses the coefficient ring `𝒮` beyond being a commutative ring, except the facts about `2` that (R1) does not need.
- **(R2)** For every `β : RA R`, `Δ`, `q`: `∃ x : R, (β * β) Δ q = (if Δ = ∅ ∧ q = 0 then β ∅ 0 * β ∅ 0 else 0) + 2 * x`.

## Part K — the reduction modulo 4

- **(K1)** For `ϑ ∈ Kr` and every `y`: `red4 (ϑ y) = red4 (ϑ 0)`.
- **(K2)** For `Γ Γ'` with `InK Γ` and `InK Γ'`, and every `h`:
  - `kap (prodFun h Γ Γ') = kap Γ * kap Γ'`;
  - `kap (Γ + Γ') = kap Γ + kap Γ'` and `kap (Γ - Γ') = kap Γ - kap Γ'` (these hold with no hypothesis);
  - `kap (fun Δ m _ => if Δ = ∅ ∧ m = 0 then (1 : ℤ_[2]) else 0) = 1`.
- **(K3)** For `InK Γ` and every `h`: `kap (GC h Γ) = kap (GB Γ)`.
- **(K4)** For `InK Γ`, `CoefB Γ` and every `h`, with `Q := rinv (h + 1) (GP h Γ)`:
  `kap (GP h Γ) * kap Q = 1` and `kap (schurG h Γ) = kap (GD Γ) - kap (GB Γ) * kap Q * kap (GB Γ)`.

## Part M — one move

For `Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]` with `Good Γ`, `Good Γ''`, `Cong2 Γ Γ''`, and every `h`:

- **(M1)** `kap (schurG h Γ) = kap (schurG h Γ'')`.
- **(M2)** `∀ Δ m y, ∃ z, schurG h Γ Δ m y - schurG h Γ'' Δ m y = 4 * z`.
- **(M3)** (C48 W5 with the Schur equation kept.) For every `Γ` with `Good Γ`, every `P h c`: `∃ Γ', Good Γ' ∧ (∀ Δ m y, 2 * Γ' Δ m y = schurG h Γ Δ m y) ∧ CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ')`.
- **(M4)** If `∀ Δ m y, 2 * Γ' Δ m y = schurG h Γ Δ m y` and `∀ Δ m y, 2 * Γ''' Δ m y = schurG h Γ'' Δ m y`, then `Cong2 Γ' Γ'''`.
- **(M5)** One twist move: for every `P h c`, `∃ Γ' Γ''', Good Γ' ∧ Good Γ''' ∧ Cong2 Γ' Γ''' ∧ CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ') ∧ CleanStep (covSys P h c Γ'') (covSys P (h + 1) c Γ''')`.
- **(M6)** One split move: for every `P h c` with `hP : h ∉ P`, `∃ Γ' Γ''', Good Γ' ∧ Good Γ''' ∧ Cong2 Γ' Γ''' ∧`
  `CleanStep (vsplit (covSys P h c Γ)) (fun q q' => covSys (insert h P) (h + 1) c Γ' (splitDn P h hP q) (splitDn P h hP q')) ∧`
  `CleanStep (vsplit (covSys P h c Γ'')) (fun q q' => covSys (insert h P) (h + 1) c Γ''' (splitDn P h hP q) (splitDn P h hP q'))`.

## Part D — Lemma 10.18 for the dance

- **(D0)** For every `P h c`, every type `n` and every `e : n → Dn P`: `Cong2 Γ Γ'' → MCong 1 (fun j j' => covSys P h c Γ'' (e j) (e j')) (fun j j' => covSys P h c Γ (e j) (e j'))`.
- **(D1) Lemma 10.18.** For every `ds : List Bool`, `r h : ℕ`, `P : Finset ℕ` with `∀ t ∈ P, t < h`, `c : ℤ_[2]`, `Γ Γ''` with `Good Γ`, `Good Γ''`, `Cong2 Γ Γ''`, every `e : Fin r ≃ Dn P` and `X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2])` with `hX : X = fun j j' => covSys P h c Γ (e j) (e j')` and `hY : Y = fun j j' => covSys P h c Γ'' (e j) (e j')`:
  `∃ Xk Yk, GlueDance.PairRel ds r X Y Xk Yk`.
- **(D2) The glued dance.** Under the hypotheses of (D1), for every `r₂` with `hr : r₂ = 2 * r` and every `Z` with `MAgree (Y - X) ((2 : ℤ_[2]) • Z)`:
  `∃ Xk Yk Zk, DanceRel ds r X Xk ∧ DanceRel ds r Y Yk ∧ MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk) ∧ DanceRel ds r₂ (GlueDance.glueC hr X Y Z) (GlueDance.glueC (GlueDance.S4 ds hr) Xk Yk Zk)`.
- **(D3)** Under the hypotheses of (D1), there is `Z` with `MAgree (Y - X) ((2 : ℤ_[2]) • Z)`.

## Proof sketch

- (R1): copy C47 `RingK/PartR.lean` (`powerset_assoc`, `range_assoc`, `sum_powerset_sdiff`, `mul_comm'`, `mul_assoc'`, `one_mul'`, `left_distrib'`, the instance) with `R` for `𝒮`.
- (R2): the involution `(Δ₁, a) ↦ (Δ \ Δ₁, q − a)` of C47 (R2). Paired terms give `2 * (…)`. A fixed point needs `Δ₁ = Δ \ Δ₁`, so `Δ = ∅`, and `q = 2a`. Then for `a ≥ 1` the factor `C(2a, a)` is even (`Nat.two_dvd_centralBinom_of_one_le`), and for `a = 0` the term is `β ∅ 0 * β ∅ 0`. Write the sum as (the fixed-point term) + 2 · (half the rest): split the index set into the fixed point, and a set `T` and its image under the involution, or prove by `Finset.sum_involution` on the residue; any route is fine.
- (K1): `ϑ = r.eval` and C47 (K6): `ϑ y − r.a = 4 z` and `ϑ 0 − r.a = 4 z'`; `red4 4 = 0` (`decide` on `ZMod (2 ^ 2)`).
- (K2): `red4` of the sum defining `prodFun` at `y = 0`; each shifted factor `Γ' (Δ \ Δ₁) (m − a) (0 − a 2^h − oS Δ₁)` reduces as at `0` by (K1). The unit system is in `Kr` (C47 T2, fourth clause) and is constant.
- (K3): (K1) at `y = 2^h`; `GB`, `GC` and `GP`, `GD` are in `InK` by C48 (W2).
- (K4): C48 (W3) gives `InK Q` and `prodFun (h + 1) (GP h Γ) Q = unit system`; apply (K2). Then `schurG = GD − prodFun (prodFun GB Q) GC` with C47 (T2) for `InK (prodFun GB Q)`, (K2) and (K3).
- (M1): in the commutative ring `RA (ZMod (2 ^ 2))`. Write `β = kap (GB Γ)`, `β'' = kap (GB Γ'')`, `p, p''` for `kap (GP …)`, `q, q''` for `kap Q`, `kap Q''`.
  - From `Cong2 Γ Γ''` at `y = 0` (and (K1) at `y = 2^h` for `GP`), `β'' = β + 2δ` and `p'' = p + 2π` for some `δ, π : RA _`.
  - `kap (GD Γ'') = kap (GD Γ)`: at `(Δ, 0)` both are `0`; at `(Δ, q + 1)` the difference is `(2q + 2) · dfi (q + 1) · 2 z ≡ 0 (mod 4)`.
  - `q'' − q = q'' q (p − p'') = −2 q'' q π` (commutative ring; `p q = 1`, `p'' q'' = 1`).
  - `β''² q'' − β² q = β² (q'' − q) + 4(…) = −2 β² q'' q π`, and `4 = 0` in `ZMod (2 ^ 2)`.
  - `β² = 2 γ` entrywise by (R2): at `(∅, 0)`, `β ∅ 0 = red4 (dfi 0 · Γ ∅ 0 0) = 0` by `PayA`. So `β²(q'' − q) = −4(…) = 0`.
- (M2): `schurG h Γ` and `schurG h Γ''` are in `InK` (proof of C48 `W4_strong`, `hS`), so by (K1) their values at `y` reduce like their values at `0`, which agree by (M1). `red4 x = 0` iff `∃ z, x = 4 z` (`PadicInt.toZModPow` kernel, or `PadicInt.ker_toZModPow` / `zmod_congr`).
- (M3): the proof of C48 (W5): it obtains `Γ'` from `W4_strong` and proves `Good Γ'`; keep the equation `2 Γ' = schurG h Γ` that `W4_strong` gives.
- (M4): `2 (Γ' − Γ''') = 4 z` and `ℤ_[2]` has no `2`-torsion.
- (M5): (M3) twice, (M2), (M4).
- (M6): `Cong2 (vsplitG h Γ) (vsplitG h Γ'')` is immediate from the definition; C48 (V2) gives `Good (vsplitG h Γ)`; then (M5) on `insert h P` at level `h` and the transport of C48 (V3) (`V1` and `L1` along `splitDn P h hP`).
- (D0): `Z j j' := ⟨fun m f => if (e j').1 ⊆ (e j).1 then z else 0⟩` with `z` chosen by `Cong2` at the point `2^h f + o_{D} + c` (classical choice), so that `Agree (covSys … Γ'' − covSys … Γ) (2 • Z)` coefficientwise. Mind the order: `MCong 1 Y X` is `Y − X`.
- (D1): by induction on `ds`, generalizing `r h P Γ Γ'' e X Y`, exactly as C48b (T2):
  - `[]`: `Xk := X`, `Yk := Y`; `MCong 1 Y X` by (D0).
  - `false :: rest`: (M5), `L1` along `e`, then the induction hypothesis at `h + 1`.
  - `true :: rest`: (M6), `L1` along `Equiv.prodCongr e (Equiv.refl (Fin 2))` after C48b (T1), the equivalence `e₂ : Fin (r * 2) ≃ Dn (insert h P)` of C48b (T2), and the induction hypothesis at `(r * 2, h + 1, insert h P)`. Note `GlueDance.relab` of the matrix `fun q q' => covSys … (splitDn P h hP ((e × id) q)) …` is `fun j j' => covSys … (e₂ j) (e₂ j')` by `rfl` (or entry by entry).
- (D2): (D1), then C50 (D1) and (D2). (D3): (D0) and the definition of `MCong` at `M = 1` (`2 ^ 1 = 2`).

## Checks before formalization

`chkC50b.py` (exact rationals with odd denominators; K-functions `a + 2 p(2y)/q(2y)` with random small integer data; `prodFun`, `rinv`, `GB`, `GC`, `GP`, `GD`, `schurG`, `vsplitG` written from their Lean definitions).
- **(K1):** 60 random K-functions are constant modulo `4` on `y = −3…3`.
- **(K2):** `prodFun h Γ Γ'` reduced modulo `4` equals the `RA (ℤ/4)` product of the values at `0` (960 entries; `h = 0…2`, `Δ ⊆ {0, 1}`, `m ≤ 3`, `y ∈ {−2, 0, 3}`).
- **(R2):** `(β * β) Δ q` is even off `(∅, 0)` for 200 random `β : RA (ℤ/4)` (9 600 entries).
- **(M2) along the dance:** good `Γ` and `Γ'' = Γ + 2E` (`E` a K-function, `2·`K at `(∅, 0)`) danced along the seven words `F, T, FF, FT, TF, TT, FTF` (`F` twist, `T` split then twist), four trials each, `m ≤ 11`: at every twist `schurG h Γ ≡ schurG h Γ'' (mod 4)` (948 entries).
- **Sanity of (W5):** the next payment `schurG ∅ 0` is `≡ 0 (mod 16)` and `schurG ∅ 1 / 2` is odd (20 systems).

Result: 11 616 checks, 0 failures (`logs/chkC50b.log`; script md5 `50985bbac5d682c90e48dd6e9301c553`). Controls, three of three fire (first twist only):
- `Γ'' = Γ + E` off `(∅, 0)`, `(∅, 1)` (not congruent modulo `2`): the Schur complements differ modulo `4` (22 of 28);
- an odd payment (so `β ∅ 0` is odd and `β²` is not even): (M2) fails (9 of 28);
- one coefficient `y ↦ 2y + 1`, not in `𝒦` (not constant modulo `4`): (M2) fails (22 of 28).
