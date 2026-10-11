# C40b — The formal dance of payment systems (paper v8 §10.3, Lemma 10.6)

*Lean piece C40b of the Dancing Sand Theorem. Grepy Escribano, 9 October 2026. Folder `RequestProject/FormalDance/`, namespace `FormalDance`. Do not change any earlier file.*

## Setting (reuse; do not redefine)

- C40 `FormalOps`: the formal operators `Bf A` (`coef : ℕ → ℤ → A`, the coefficient of `F^{(m)}` at the target floor; product `(x*y).coef m f = Σ_{a ≤ m} C(m,a) x.coef a f * y.coef (m−a) (f−a)`), `Bf.fd`, `Bf.dg`, the ring instance `Bf.instRing`, the scalar action of `A`, the twist map `tw00`, `tw11`, `tw10`, `tw01`, the V-split `vplus`, `vprime`, `flD`, `act`, and the theorems `B4`, `T1`, `V1`.
- C11 `Payment.pT`, `Payment.κT` (the twisted data). C12 `Split.pSp`, `Split.κSp` (the split data, on `Lex (S × Fin 2)`).
- C13 `Dance.slots`, `Dance.slots_eq`, `Dance.splitIso`, `Dance.relabP`, `Dance.relabK`, `Dance.danceAux`, `Dance.dance`, `Dance.Mfin`, `Dance.pσ`, `Dance.κσ`, `Dance.mCount`.
- C20 `Doubling.dfi` (`dfi 0 = 1`, `dfi 1 = 1` over every commutative ring).

`A` is any commutative ring unless said otherwise. Index types `n` of systems are `Fintype`, `DecidableEq`, and carry a `LinearOrder` when payment systems are built on them. Matrices over `Bf A` use Mathlib's `Matrix n n (Bf A)` with its ring structure (`Bf A` is not commutative; that is fine).

## Definitions (new)

1. **Agreement.** `Agree (x y : Bf A) : Prop := ∀ (m : ℕ) (f : ℤ), (m : ℤ) ≤ f → x.coef m f = y.coef m f`. (Only the values `x_m(g)` with `g ≥ m` act on a lattice; the paper identifies formal sums that agree there.) For matrices, `MAgree (G H : Matrix n n (Bf A)) : Prop := ∀ s s', Agree (G s s') (H s s')`.
2. **Extension by zero.** `ext0 (q : ℕ → A) : ℤ → A := fun f => if 0 ≤ f then q f.toNat else 0`.
3. **Payment systems.** For `p : n → ℕ → A`, `κ : n → n → ℕ → A`:
   `paySys p κ : Matrix n n (Bf A) := fun s s' => if s = s' then Bf.fd 1 + Bf.dg (ext0 (fun f => 2 * p s f)) else if s' < s then Bf.dg (ext0 (fun f => 2 * κ s s' f)) else 0`.
   (`G[s, s']` maps the source slot `s'` to the coordinate slot `s`; this is `F + 2π(D) + 2K(D)`, the operator `Payment.G` with halved data.)
4. **Twist blocks** of a system `G : Matrix n n (Bf A)` (entrywise): `twP G s s' := tw10 (G s s')`, `twC G s s' := tw11 (G s s')`, `twB G s s' := tw00 (G s s')`, `twD G s s' := tw01 (G s s')`. (Pivot `P = G^{10}`, `C = G^{11}`, `B = G^{00}`, `Dd = G^{01}`, as in the paper: coordinates `b_1`-slots then `b_0`-slots, sources `b_0`-slots then `b_1`-slots; compare C40 `T1`.)
5. **V-split** of a system: `vsplit G : Matrix (n × Fin 2) (n × Fin 2) (Bf A) := fun (s, v) (s', v') => if v = 0 ∧ v' = 0 then G s s' else if v = 1 ∧ v' = 0 then vprime (G s s') else if v = 1 ∧ v' = 1 then vplus (G s s') else 0`. (The block `[[x, 0], [x', x⁺]]`; compare C40 `V1`.)
6. **A clean move.** `CleanStep (G G' : Matrix n n (Bf A)) : Prop := ∃ Q : Matrix n n (Bf A), MAgree (twP G * Q) 1 ∧ MAgree (Q * twP G) 1 ∧ MAgree (twD G - twB G * Q * twC G) ((2 : A) • G')`. (`P` invertible up to agreement, `S := Dd − B P⁻¹ C`, and `S = 2 G'`.)
7. **The formal dance**, a relation defined by recursion on `ds : List Bool`:
   `DanceRel : (ds : List Bool) → (r : ℕ) → Matrix (Fin r) (Fin r) (Bf A) → Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A) → Prop`,
   - `DanceRel [] r G Gk := MAgree G Gk`;
   - `DanceRel (false :: rest) r G Gk := ∃ G', CleanStep G G' ∧ DanceRel rest r G' Gk` (a twist move);
   - `DanceRel (true :: rest) r G Gk := ∃ G'' : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf A), CleanStep (vsplit G) G'' ∧ DanceRel rest (r * 2) (fun j j' => G'' (ofLex ((Dance.splitIso r).symm j)) (ofLex ((Dance.splitIso r).symm j'))) Gk` (a split move: V-split, then twist, then the relabelling of C13).
   `Clean ds r G := ∃ Gk, DanceRel ds r G Gk`.
8. **The final matrix.** `finalM (Gk : Matrix m m (Bf A)) : Matrix m m A := fun s s' => (Gk s s').coef 0 0`. (On `T(0) = A` the formal operator acts by its coefficient of `F^{(0)}` at the floor `0`.)

## Statements to prove

### Part C — agreement is a congruence
- **(C1)** `Agree` and `MAgree` are equivalence relations.
- **(C2)** If `Agree x x'` and `Agree y y'` then `Agree (x + y) (x' + y')`, `Agree (x - y) (x' - y')`, `Agree (x * y) (x' * y')`, `Agree (a • x) (a • x')` for `a : A`. The same for `MAgree` with matrix sum, difference, product (over `Fintype n`) and `A`-scalar multiplication.
- **(C3)** If `Agree x y` then `Agree (tw00 x) (tw00 y)`, the same for `tw11`, `tw10`, `tw01`, `vplus`, `vprime`. Hence `MAgree G H` implies `MAgree` of `twP`, `twC`, `twB`, `twD` and of `vsplit`.
- **(C4)** (agreement does not change the action) If `N : DPLattice A` satisfies (top W) `∀ i, N.wt i ≤ W ∧ Even (W − N.wt i)` and `Agree x y`, then `act N W B x = act N W B y` for every `B`.
  *(Sketch: by C18 (W) `N.Fd m` lowers the weight by `2m`, so it raises the floor `(W − wt)/2` by `m`; floors are `≥ 0` under (top W), so `flD` reads `x.coef m` only at floors `≥ m`.)*

### Part L — Lemma 10.6
- **(L1) The twist move of a payment system** (Lemma 10.6(a), first sentence). For `p : n → ℕ → A`, `κ : n → n → ℕ → A`:
  `twP (paySys p κ) = 1` and `twD (paySys p κ) - twB (paySys p κ) * twC (paySys p κ) = (2 : A) • paySys (Payment.pT p) (Payment.κT p κ)` (exact equalities). Consequently `CleanStep (paySys p κ) (paySys (Payment.pT p) (Payment.κT p κ))`.
- **(L2) The split move of a payment system** (Lemma 10.6(a), second sentence). With `pS := fun (q : n × Fin 2) => Split.pSp p (toLex q)` and `κS := fun (q q' : n × Fin 2) => Split.κSp p κ (toLex q) (toLex q')`, and the payment system on `n × Fin 2` taken with the lexicographic order, i.e. `PS := fun q q' => paySys (Split.pSp p) (Split.κSp p κ) (toLex q) (toLex q')` (a matrix on `Lex (n × Fin 2)` read through `toLex`):
  `twP (vsplit (paySys p κ)) = 1` and `MAgree (twD (vsplit (paySys p κ)) - twB (vsplit (paySys p κ)) * twC (vsplit (paySys p κ))) ((2 : A) • PS)`. Consequently `CleanStep (vsplit (paySys p κ)) PS`.
- **(L3) Relabelling.** For an order isomorphism `e : n ≃o n'`, `(paySys (Dance.relabP e p') (Dance.relabK e κ')) = fun s s' => paySys p' κ' (e s) (e s')`.
- **(L4) The formal dance of a payment system is the data dance** (Lemma 10.6(b)). For every `ds`, `r`, `p : Fin r → ℕ → A`, `κ : Fin r → Fin r → ℕ → A`:
  `DanceRel ds r (paySys p κ) (paySys (Dance.danceAux ds r p κ).1 (Dance.danceAux ds r p κ).2)`; and `finalM (paySys p' κ') = Dance.Mfin p' κ'` for every `p'`, `κ'` on `Fin R`.
  Hence for `σ`: `Clean ds 1 (paySys (Dance.pσ α i) Dance.κσ)`, and the witness `Gk` above satisfies, for all `t t' : Fin (1 * 2 ^ Dance.mCount ds)`,
  `finalM Gk (Fin.cast (Dance.slots_eq ds 1).symm t) (Fin.cast (Dance.slots_eq ds 1).symm t') = Dance.Mfin (Dance.dance ds 1 (Dance.pσ α i) Dance.κσ).1 (Dance.dance ds 1 (Dance.pσ α i) Dance.κσ).2 t t'`,
  which by C14 is the matrix `M^{(α)}(l, c)` of Theorem 4.4.
- **(L5) Uniqueness.** If `∀ a : A, 2 * a = 0 → a = 0`, then `DanceRel ds r G Gk` and `DanceRel ds r G Gk'` imply `MAgree Gk Gk'`, hence `finalM Gk = finalM Gk'`.
- **(L6) Scaling** (Lemma 10.6(b), last sentence). If `IsUnit u` (`u : A`) and `DanceRel ds r G Gk`, then `DanceRel ds r (u • G) (u • Gk)`, and `finalM (u • Gk) = u • finalM Gk`.
  *(Sketch: the twist map and the V-split commute with `u •`; take `Q' := u⁻¹ • Q`; then `S' = u • S`.)*

## Proof sketches
- (L1): on the diagonal `x = fd 1 + dg(2p)`: `tw10 x` has `coef 0 f = dfi 1 · x.coef 1 (2f+1) = 1` and `coef q = 0` for `q ≥ 1`; `tw01 x = 2 • fd 1` (`coef 1 f = 2 · dfi 1 · x.coef 1 (2f)`); `tw00 x = dg(2p(2·))`, `tw11 x = dg(2p(2·+1))` (with `ext0`: `2f ≥ 0 ⟺ f ≥ 0 ⟺ 2f+1 ≥ 0`). Below the diagonal only `coef 0` is non-zero, so `tw10 = tw01 = 0` there. Then `B * C` is a product of lower-triangular matrices of `dg`'s, `dg a * dg b = dg (a * b)`, and its entries are `4 ×` the bracket of `κT` (diagonal: `4 p(2f) p(2f+1)`), giving `Dd − B C = 2 • paySys (pT p) (κT p κ)`.
- (L2): the same computation on `vsplit`, with the `vplus` / `vprime` shifts; the pivot is again exactly `1`; equality holds at every floor `f ≥ m` (agreement). Compare C12 `Split.pSp_A`, `pSp_C`, `κSp_AA`, `κSp_CC`, `κSp_CA`, `κSp_AC`.
- (L4): induction on `ds`, generalizing `r`, `p`, `κ`; use (L1), (L2), (L3) and `Dance.danceAux` by `rfl` on each cons.
- (L5): induction on `ds`; two inverses of `P` up to agreement agree; `2 • G' ~ 2 • G''` and no 2-torsion give `G' ~ G''`; then (C2), (C3).

## Checks done before sending
- Brute force `chkC40b.py` (exact rationals; formal operators as tables `(m, f) ↦ x_m(f)`; payment systems with random integer data on 1–3 slots): (L1) `P = 1` exactly and `Dd − BC = 2 paySys(pT, κT)` exactly; (L2) `P = 1` exactly and `Dd − BC ~ 2 paySys(pSp, κSp)` (agreement); (C2)–(C3) congruence with random junk at floors `f < m`; (L4) the formal dance of `σ^{(α)}_i` on `T(l)`, `l ≤ 15`, `α ≤ 3`, `i ∈ {0, 1, 2, 5}`, final matrix `= Mfin(dance)` of the data recursion; (L6) `u = 3, −1`. **412 checks, 0 failures.** `logs/chkC40b.log`.
- Controls (all six fire): `κT` with the middle sum in the wrong order; the pivot read from `tw11`; the split data without the floor shift on the `C` slots; the dance with split steps taken as twist steps; the V-split with `vplus` and `vprime` exchanged; a change of `x_1` at a floor `f ≥ 1` breaks agreement of the product.
- Observation, not claimed: in every sample of (L2) the equality was exact also at the floors `−2 ≤ f < m`; only agreement is stated.

## Notes
- Lemma 10.6(b) says «the dance of `σ^{(α)}_c` on `T(l)` is clean and `M_w(σ^{(α)}_c) = M^{(α)}(l, c)`»: here this is (L4) for `r = 1` together with C14's identification of `Mfin (dance …)` with the matrix of Theorem 4.4; the C14 theorem is cited, not restated.
- Proposition 10.7 (the cokernel count through the action on `T(l)`) is the next piece, C40c.
