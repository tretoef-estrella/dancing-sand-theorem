# Congruence along the dance, and the data of Ξ at c = 0 (paper v8 §10.6, first half)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §10.6, proof of Theorem 10.16, the case `c = 0`. The paper argues by continuity in `c`. This piece replaces continuity by congruences, which is the same argument written with exact divisibility:
- if two systems agree modulo `2^{M+k}`, their final matrices after a dance of `k` moves agree modulo `2^M`, because every move divides by `2` once;
- `Ξ` at `c = 0` and at `c = 2^N` agree modulo `2^{α+N}`;
- at `c = 2^N ≥ 1` the entries of the final matrix of `Ξ` have the norms of the integer final matrix `M^{(α)}(l, 2^N)` (C46 (V1));
- that matrix agrees with `M^{(α)}(l, 0)` modulo `2^{α+N−k}` (the same transport, on the payment system of `σ`).

Letting `N` grow gives the data at `c = 0`: **the final matrix of `Ξ` at `c = 0` has, entry by entry, the norms (so the zeros and the valuations) of `M^{(α)}(l, 0)`.** The Smith form and the cokernel at `c = 0` are the next piece (C49c).

Folder `RequestProject/ContZero/`, namespace `ContZero`. Nothing of the project is redefined.

## Setting (reused, without changing them)

- C40 `FormalOps`: `Bf`, `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`, `Bf.dg`, `Bf.fd`.
- C40b `FormalDance`: `Agree`, `MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `DanceRel`, `finalM`, `paySys`, `ext0`, and its results on `Agree`/`MAgree` (equivalence, congruence for `+`, `−`, `*`, scalars and for the twist blocks and `vsplit`), (L4) `L4_sigma`.
- C20 `Doubling.dfi`, the instance `Doubling.OddUnits ℤ_[2]`.
- C13 `Dance`: `pσ`, `κσ`, `slots`, `splitIso`, `mCount`, `dance`, `Mfin`.
- C14 `Windows`: `finalMatrix`, `finalMatrix_eq_map`, `theorem_D_ii`, `Dset`.
- C15 `DanceSmith`: `sl`, `zeroPos`, `final_row_zero`.
- C46 `Smith2`: `XiOpZ`, `slots_cast`, (V1).
- C48b `DanceXi`: (T3).
- C32 `Families.ds`; C44 `Stability.length_ds_pos`.

## Definitions (new)

- `Cong (M : ℕ) (x y : Bf ℤ_[2]) : Prop := ∃ z : Bf ℤ_[2], Agree (x - y) ((2 : ℤ_[2]) ^ M • z)`.
- `MCong {n : Type*} (M : ℕ) (G H : Matrix n n (Bf ℤ_[2])) : Prop := ∃ Z : Matrix n n (Bf ℤ_[2]), MAgree (G - H) ((2 : ℤ_[2]) ^ M • Z)`.

## Part K — congruences in `Bf ℤ_[2]`

- **(K1)** `Cong M` is reflexive, symmetric and transitive; `Agree x y → Cong M x y`; `Cong M x y → M' ≤ M → Cong M' x y`; if `Cong M x x'` and `Cong M y y'` then `Cong M (x + y) (x' + y')`, `Cong M (x - y) (x' - y')`, `Cong M (x * y) (x' * y')`, and `Cong M (a • x) (a • x')` for `a : ℤ_[2]`.
- **(K2)** If `Cong M x y`, then `Cong M (tw00 x) (tw00 y)`, the same for `tw11`, `tw10`, `tw01`, `vplus` and `vprime`.
- **(K3)** For `Fintype n` with `DecidableEq n`: `MCong M` is reflexive, symmetric and transitive; `MAgree G H → MCong M G H`; `MCong M G H → M' ≤ M → MCong M' G H`; it is compatible with `+`, `−`, `*` (matrix product) and scalars of `ℤ_[2]`; if `MCong M G H` then `MCong M (twP G) (twP H)`, the same for `twC`, `twB`, `twD`, and `MCong M (vsplit G) (vsplit H)`; and for `e : n' ≃ n`, `MCong M G H → MCong M (fun j j' => G (e j) (e j')) (fun j j' => H (e j) (e j'))`.
- **(K4) Inverses.** If `MAgree (P * Q) 1`, `MAgree (Q * P) 1`, `MAgree (P' * Q') 1`, `MAgree (Q' * P') 1` and `MCong M P P'`, then `MCong M Q Q'`.
- **(K5) Halving.** If `MCong (M + 1) ((2 : ℤ_[2]) • G) ((2 : ℤ_[2]) • H)` then `MCong M G H`.
- **(K6) One clean move.** If `CleanStep G G'`, `CleanStep H H'` and `MCong (M + 1) G H`, then `MCong M G' H'`.

## Part T — transport along the dance

- **(T1)** For every `ds : List Bool`, `r M : ℕ`, `G H : Matrix (Fin r) (Fin r) (Bf ℤ_[2])` and `Gk Hk`: if `DanceRel ds r G Gk`, `DanceRel ds r H Hk` and `MCong (M + ds.length) G H`, then `MCong M Gk Hk`.
- **(T2) The final matrices.** If `MCong M Gk Hk` (any index type `m`), then for all `s s'` there is `w : ℤ_[2]` with `finalM Gk s s' - finalM Hk s s' = 2 ^ M * w`.
- **(T3) Uniqueness.** If `DanceRel ds r G Gk` and `DanceRel ds r G Hk`, then `finalM Gk = finalM Hk`.

## Part C — the shift `c` moves the systems by multiples of `2^{α+N}`

- **(C1)** For `α c c' N : ℕ` with `(2 : ℤ) ^ N ∣ (c' : ℤ) - c`, every `η : ℤ_[2]` and every `ζ : ℕ → ℤ → ℤ_[2]`: `Cong (α + N) (Smith2.XiOpZ α c η ζ) (Smith2.XiOpZ α c' η ζ)`.
- **(C2)** Under the same hypothesis on `c, c', N` and `1 ≤ α`: `MCong (α + N) (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ) (paySys (Dance.pσ (A := ℤ_[2]) α c') Dance.κσ)`.
- **(C3) The integer final matrices.** For `1 ≤ α`, every `ds : List Bool`, `c c' N M : ℕ` with `(2 : ℤ) ^ N ∣ (c' : ℤ) - c` and `M + ds.length = α + N`: for all `s s'`, `(2 : ℤ) ^ M ∣ Windows.finalMatrix ℤ ds α c s s' - Windows.finalMatrix ℤ ds α c' s s'`.

## Part V — the data of `Ξ` at `c = 0`

Hypotheses (H0): `1 ≤ l`, `2 ≤ α`, `η : ℤ_[2]` with `IsUnit η`, `z : ℕ → ℤ_[2]`, and `GkZ` with `DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ`. Write `cs := Fin.cast (Smith2.slots_cast (Families.ds l))`.

- **(V1) Norms.** Under (H0), for all `s s' : Fin (2 ^ Dance.mCount (Families.ds l))`:
  `‖finalM GkZ (cs s) (cs s')‖ = ‖((Windows.finalMatrix ℤ (Families.ds l) α 0 s s' : ℤ) : ℤ_[2])‖`.
- **(V2) Zeros.** Under (H0): `finalM GkZ (cs s) (cs s') = 0 ↔ Windows.finalMatrix ℤ (Families.ds l) α 0 s s' = 0`.
- **(V3) The row of `∅`.** Under (H0): for every `s'`, `finalM GkZ (cs (DanceSmith.sl (Families.ds l) (DanceSmith.zeroPos (Families.ds l)))) (cs s') = 0`; hence the matrix `X s s' := finalM GkZ (cs s) (cs s')` on `Fin (2 ^ Dance.mCount (Families.ds l))` has `X.det = 0`.

## Proof sketch

- (K1), (K3): `Agree` and `MAgree` are equivalence relations and congruences (C40b); the multiples `2^M • z` form an ideal: `(2^M • z) * w = 2^M • (z * w)`, and a difference of products is `x y − x' y' = (x − x') y + x' (y − y')`. Lowering `M`: `2^M • z = 2^{M'} • (2^{M − M'} • z)`.
- (K2): all six maps are additive, commute with scalars of `ℤ_[2]` (each coefficient of the image is `dfi q` times, or equal to, one coefficient of the argument), and preserve `Agree` (C40b (C3)).
- (K4): `Q − Q' ≈ Q (P' − P) Q'` up to `MAgree` (expand with `Q P ≈ 1`, `P' Q' ≈ 1`), and `P' − P ≈ −2^M • Z`.
- (K5): coefficientwise `2 a = 2^{M+1} b` with `a, b ∈ ℤ_[2]` gives `a = 2^M b`, since `ℤ_[2]` has no zero divisors; `Agree` is a statement on coefficients, so `MAgree ((2 : ℤ_[2]) • (G − H)) (2^{M+1} • Z)` gives `MAgree (G − H) (2^M • Z)`.
- (K6): with `Q, Q'` the inverses of `twP G`, `twP H` from the two clean steps, (K3) and (K4) give `MCong (M + 1) (twD G − twB G * Q * twC G) (twD H − twB H * Q' * twC H)`, that is `MCong (M + 1) (2 • G') (2 • H')`; then (K5).
- (T1): induction on `ds`, generalizing `r, G, H, Gk, Hk`. `[]`: `MAgree G Gk`, `MAgree H Hk`, `MCong M G H`. `false :: rest`: (K6) with `M + rest.length`, then the induction hypothesis. `true :: rest`: (K3) for `vsplit`, (K6), reindexing along `ofLex ∘ (Dance.splitIso r).symm` by (K3), then the induction hypothesis.
- (T2): `finalM` reads the coefficient `(0, 0)`, and `Agree` covers `m = 0 ≤ f = 0`.
- (T3): (T1) with `H := G` and every `M`, then (T2): the difference is divisible by every power of `2`, so it is `0` (`PadicInt`: an element of norm `≤ 2^{−M}` for all `M` is `0`).
- (C1): the two series differ only in the coefficient `m = 0`, where the difference is `2^α ((f : ℤ_[2]) + c) − 2^α ((f : ℤ_[2]) + c') = 2^α (c − c') = 2^{α+N} t` for an integer `t`; take `z := Bf.dg (fun _ => −t)` (or the series with that coefficient at `m = 0` and `0` elsewhere).
- (C2): only the diagonal entries differ, in `Bf.dg (ext0 (fun f => 2 * pσ α c 0 f))`, by `ext0 (fun _ => 2 · 2^{α−1} (c − c'))`, i.e. `2^α (c − c')` for `f ≥ 0` and `0` for `f < 0`.
- (C3): (L4) `L4_sigma` over `ℤ_[2]` at `c` and at `c'` gives two dances whose final matrices are `Mfin (dance …)` read through `Fin.cast`; by `Windows.finalMatrix` and `finalMatrix_eq_map` these entries are the integers `finalMatrix ℤ ds α c s s'` cast to `ℤ_[2]`. (C2), (T1), (T2) give `2^M` dividing the difference in `ℤ_[2]`; for integers this is divisibility in `ℤ` (`‖(n : ℤ_[2])‖ ≤ 2^{−M} ↔ 2^M ∣ n`).
- (V1): put `a := finalM GkZ (cs s) (cs s')`, `b := (finalMatrix ℤ ds α 0 s s' : ℤ_[2])`, `k := ds.length ≥ 1`. For every `N`, take a dance `GkN` of `XiOpZ α (2^N) η (fun m _ => z m)` (C48b (T3)) and put `a_N`, `b_N` the same entries at `c = 2^N`. Then `‖a − a_N‖ ≤ 2^{−(α+N−k)}` by (C1), (T1), (T2), and `‖b − b_N‖ ≤ 2^{−(α+N−k)}` by (C3). And `‖a_N‖ = ‖b_N‖`: on nested pairs by C46 (V1) at `c = 2^N ≥ 1`; off nested pairs both are `0` (C46 (V1) and `theorem_D_ii`). If `b ≠ 0`, choose `N` with `2^{−(α+N−k)} < ‖b‖`; then `‖b_N‖ = ‖b‖`, so `‖a_N‖ = ‖b‖`, so `‖a‖ = ‖b‖` (ultrametric). If `b = 0`, `‖a‖ ≤ max(‖a_N‖, 2^{−(α+N−k)}) = max(‖b_N‖, 2^{−(α+N−k)}) ≤ 2^{−(α+N−k)}` for every `N`, so `a = 0`.
- (V2): from (V1), `‖x‖ = 0 ↔ x = 0` and the cast `ℤ → ℤ_[2]` is injective.
- (V3): `DanceSmith.final_row_zero` (`1 ≤ α`) and (V2); a matrix with a zero row has determinant `0`.

## Checks before formalization

`chkC49b.py` (md5 `e0c53f2a5de479e854440520b4e7e25c`; exact rationals, the lattice model of `chkC43.py` and the lattice dance of `chkC48b.py`).
- **Cells:** `l = 1…9`, `α = 2, 3`, four random units `η` and random constant `z_m` with odd denominators in each (72 cells).
- **Agreement of the systems:** `Ξ_0` and `Ξ_{2^N}` on `T(l)` agree modulo `2^{N+α}` (`N = 3, 5, 8`).
- **Transport:** their final matrices agree modulo `2^{N+α−k}`, `k` = the number of moves; the same holds for `σ_0` and `σ_{2^N}`.
- **The data at `c = 0`:** the final matrix of `Ξ_0` has exactly the zeros and the entry valuations of the final matrix of `σ_0`.
- **Smith forms at `c = 0`:** the Smith exponents of the two final matrices are equal, with one infinite exponent, and so are those of `Ξ_0` and `σ_0` on `T(l)`.

Result: 1 464 checks, 0 failures.

Controls, three of three fire:
- `η = 2` (not a unit);
- `α = 1`;
- the support of `σ_1` in place of `σ_0`.

Observation, not a control: the bound `N + α − k` was never tight in these cells. The loss of one power of `2` per move is what the proof gives, not what happens in practice.
