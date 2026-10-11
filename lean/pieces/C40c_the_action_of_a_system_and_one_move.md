# C40c — The action of a system on a lattice, and one move of the dance (paper v8 §10.3, proof of Proposition 10.7, one step)

*Lean piece C40c of the Dancing Sand Theorem. Grepy Escribano, 9 October 2026. Folder `RequestProject/FormalAct/`, namespace `FormalAct`. Do not change any earlier file.*

Proposition 10.7 says: if the dance of a system `G` of size `r` on `T(l)` is clean, then `coker(G on T(l)^{⊕r}) ≅ ⊕_{a=1}^{k−1} (ℤ/2^a)^{r·2^{|I|+k−1−a}} ⊕ coker(2^k M_w(G))`. Its proof is one step repeated: `coker(2^h G_h) ≅ (ℤ/2^h)^{rank P} ⊕ coker(2^{h+1} G_{h+1})`. This piece proves that step, for a twist move and for a split move, on every DP-lattice; the induction along `T(l)` and the count of ranks are the next piece (C40d).

## Setting (reuse; do not redefine)

- C18 `DPLattice` (fields `ι`, `wt`, `Fd`, `Ed`, with (W): `Fd r` lowers the weight by `2r`), `DPLattice.one`, `DPLattice.bvec`, `DPLattice.slice`, `DPLattice.tensorV`.
- C20 `Doubling.phi` (over `[IsDomain A] [CharZero A] [OddUnits A]`), `Doubling.dfi`.
- C29 `Filt.T` (the dance lattices: `T 0 = one A`, `T (2l+1) = phi (T l)`, `T (2l+2) = tensorV (phi (T l))`, theorems `T_zero`, `T_odd`, `T_even`).
- C40 `FormalOps`: `Bf A`, `flD`, `act`, `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`, `blockOp`, `schur`, and the theorems `B4`, `T0`, `T1`, `V0`, `V1`, `S1`, `S2`, `S3`.
- C40b `FormalDance`: `Agree`, `MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `finalM`, and the theorems `C1`–`C4`.

Conditions on a lattice `N` (as in C40): (top W) `∀ i, N.wt i ≤ W ∧ Even (W − N.wt i)`; (nil BN) `∀ s ≥ BN, N.Fd s = 0`. Index types `n` of systems are `Fintype` with `DecidableEq`. `A` is any commutative ring unless said otherwise.

## Definitions (new)

1. **The action of a system.** For `N : DPLattice A`, `W : ℤ`, `B : ℕ`, `G : Matrix n n (Bf A)`:
   `sysAct N W B G : (n → N.ι → A) →ₗ[A] (n → N.ι → A)`, `(sysAct N W B G v) s = Σ_{s'} act N W B (G s s') (v s')`.
   (`G[s, s']` maps the source slot `s'` to the coordinate slot `s`, as in C40b.)
2. **Packing the two halves.** For a type `ι`:
   `pack : (n → ι → A) × (n → ι → A) ≃ₗ[A] (n → Fin 2 × ι → A)`, `pack (u, v) = fun s => bvec 0 (u s) + bvec 1 (v s)`;
   `vpack : (n × Fin 2 → ι → A) ≃ₗ[A] (n → Fin 2 × ι → A)`, `vpack w = fun s => bvec 0 (w (s, 0)) + bvec 1 (w (s, 1))`.
   (The inverses read the slots with `slice 0`, `slice 1`.)

## Statements to prove

### Part N — the dance lattices
- **(N1)** If `N` satisfies (nil BN), then `phi N` satisfies (nil (2 * BN)).
- **(N2)** For every `l : ℕ`, `T A l` satisfies (top l) and (nil (l + 1)) (with `W = (l : ℤ)`).

### Part A — the action of a system
- **(A1)** (agreement) If `N` satisfies (top W) and `MAgree G H`, then `sysAct N W B G = sysAct N W B H` for every `B`.
- **(A2)** (a ring map) If `N` satisfies (nil BN), `BN ≤ B` and `1 ≤ B`, then `sysAct N W B 1 = LinearMap.id`, `sysAct N W B (G * H) = sysAct N W B G ∘ₗ sysAct N W B H`, `sysAct N W B (G + H) = sysAct N W B G + sysAct N W B H`, `sysAct N W B (G − H) = sysAct N W B G − sysAct N W B H`, and `sysAct N W B (a • G) = a • sysAct N W B G` for `a : A`.
- **(A3)** (relabelling) For `e : n ≃ n'` and `G : Matrix n' n' (Bf A)`, with `G_e := fun j j' => G (e j) (e j')`: `sysAct N W B G_e` and `sysAct N W B G` are conjugate by the reindexing `LinearEquiv.funCongrLeft` along `e`; hence for every `c : A`, `Nonempty (((n → N.ι → A) ⧸ range (c • sysAct N W B G_e)) ≃ₗ[A] ((n' → N.ι → A) ⧸ range (c • sysAct N W B G)))`.
- **(A4)** (the last level) On `one A` with `W = 0` and `1 ≤ B`: `sysAct (one A) 0 B G v s () = Σ_{s'} finalM G s s' * v s' ()`. Hence for every `c : A`, `Nonempty (((n → Unit → A) ⧸ range (c • sysAct (one A) 0 B G)) ≃ₗ[A] ((n → A) ⧸ range (c • Matrix.mulVecLin (finalM G))))`.

### Part T — the twist map and the V-split on systems
- **(T1)** Over `[IsDomain A] [CharZero A] [OddUnits A]`: if `N` satisfies (top W) and (nil BN), `2 * BN ≤ B` and `BN ≤ B'`, then for all `u v : n → N.ι → A`,
  `sysAct (phi N) (2 * W + 1) B G (pack (u, v)) = pack (sysAct N W B' (twB G) u + sysAct N W B' (twD G) v, sysAct N W B' (twP G) u + sysAct N W B' (twC G) v)`.
  (The source `b_0` gives `B` to the coordinate `b_0` and the pivot `P` to the coordinate `b_1`; the source `b_1` gives `Dd` and `C`; compare C40 `T1`.)
- **(T2)** If `M` satisfies (nil BN), `BN + 1 ≤ B` and `BN ≤ B'`, then
  `sysAct (tensorV M) (W + 1) B G ∘ₗ vpack = vpack ∘ₗ sysAct M W B' (vsplit G)`.
  (Compare C40 `V1`.)

### Part S — one move of the dance
- **(S1) A twist move.** Over `[IsDomain A] [CharZero A] [OddUnits A]`: if `N` satisfies (top W) and (nil BN), `2 * BN ≤ B`, `BN ≤ B'`, `1 ≤ B'`, and `CleanStep G G'`, then for every `h : ℕ`
  `Nonempty (((n → (phi N).ι → A) ⧸ range ((2 : A) ^ h • sysAct (phi N) (2 * W + 1) B G)) ≃ₗ[A] (((n → N.ι → A) ⧸ ((2 : A) ^ h • ⊤ : Submodule A (n → N.ι → A))) × ((n → N.ι → A) ⧸ range ((2 : A) ^ (h + 1) • sysAct N W B' G'))))`.
- **(S2) A split move.** Over `[IsDomain A] [CharZero A] [OddUnits A]`: if `N` satisfies (top W) and (nil BN), `2 * BN + 1 ≤ B`, `BN ≤ B'`, `1 ≤ B'`, and `CleanStep (vsplit G) G''` with `G'' : Matrix (n × Fin 2) (n × Fin 2) (Bf A)`, then for every `h : ℕ`
  `Nonempty (((n → (tensorV (phi N)).ι → A) ⧸ range ((2 : A) ^ h • sysAct (tensorV (phi N)) (2 * W + 2) B G)) ≃ₗ[A] (((n × Fin 2 → N.ι → A) ⧸ ((2 : A) ^ h • ⊤ : Submodule A (n × Fin 2 → N.ι → A))) × ((n × Fin 2 → N.ι → A) ⧸ range ((2 : A) ^ (h + 1) • sysAct N W B' G''))))`.

## Proof sketches
- (N1): by C20 the operators of `phi N` send `b_0 n` and `b_1 n` into `b_e F^{(q)} n` with `q ≥ ⌊m/2⌋` for `F^{(m)}`; or by (W): the weights of `phi N` are `2w ± 1`. (N2): induction on `l` with `T_zero`, `T_odd`, `T_even`, C40 `T0` and `V0`, and (N1); `nil (l+1)`: `one A` has (nil 1), and `2(l'+1) = l + 1` for `l = 2l'+1`, `2(l'+1) + 1 = l + 1` for `l = 2l'+2`.
- (A1): C40b `C4` entrywise. (A2): C40 `B4` entrywise, with `Finset.sum_comm` for the product. (A3), (A4): direct; for (A4) `act (one A) 0 B x = flD (x.coef 0)` because `Fd 0 = 1` and `Fd m = 0` for `m ≥ 1`, and the floor of the single vector is `(0 − 0)/2 = 0`.
- (T1): C40 `T1` entrywise, and linearity of `bvec`. (T2): C40 `V1` entrywise, with `vsplit` read slot by slot.
- (S1): by (T1), `sysAct (phi N) … G` is conjugate (by `pack` on the sources and `pack ∘ swap` on the coordinates) to `(u, v) ↦ (P u + C v, B u + Dd v)` with `P = sysAct (twP G)`, …. With `Q` from `CleanStep`, (A1) and (A2) give `P ∘ sysAct Q = id = sysAct Q ∘ P`, so `P` is a linear equivalence with inverse `sysAct Q`, and `schur = sysAct (twD G − twB G * Q * twC G) = sysAct ((2 : A) • G') = (2 : A) • sysAct G'`. Then C40 `S3`, and transport the cokernels along the two equivalences.
- (S2): by (T2) (with `M = phi N`, top `2W + 1`, nil `2BN` from (N1)), `sysAct (tensorV (phi N)) … G` is conjugate by `vpack` to `sysAct (phi N) (2W+1) B'' (vsplit G)`; then (S1) for `vsplit G` on the index type `n × Fin 2`.

## Checks done before sending
- Brute force `chkC40c.py` (exact rationals; lattice model of `T(λ)`, `Φ`, `V ⊗ −` with `F^{(r)} = F^r / r!`; formal operators as tables; 2-adic Smith forms over `ℤ`): (N2) `T(l)` has (top l) and (nil (l+1)) for `l ≤ 12`; (N1) for `l ≤ 6`; (A1) junk at floors `f < m` does not change `sysAct`; (A2) unit, product, difference, scalar on `T(m)`, `m ≤ 3`, sizes 1–2; (A4) sizes 1–3; (T1) on `Φ(T(m))`, (T2) on `V ⊗ Φ(T(m))` and `V ⊗ T(m)`, entry by entry, `m ≤ 2`, sizes 1–2; (S1) and (S2) with payment systems (the next systems `paySys(pT, κT)` and `paySys(pSp, κSp)` of C40b) on `T(m)`, `m ≤ 3`, sizes 1–3, `h = 0, 1, 2`, by 2-adic Smith forms; (S1) also for a unit multiple. **184 checks, 0 failures.** `logs/chkC40c.log`.
- Controls (all six fire): (N2) with (nil l) instead of (nil (l+1)); (T1) with `B` and `Dd` exchanged; (S1) without the summand `(A/2^h)^{rank}`; (S2) with `2^h` instead of `2^{h+1}` on the next system; (A4) reading the coefficient at the floor 1; (S1) with the next system of other data.

## Notes
- Proposition 10.7 itself (the induction along `T(l)` and `Families.ds l`, and the count `r·2^{|I|+k−1−a}`) is the next piece, C40d.
- In (S1) the sources are ordered (`b_0`, `b_1`) and the coordinates (`b_1`, `b_0`), as in the paper; the conjugation by `pack` and by `pack` composed with the swap of the two halves is part of the proof, not of the statement.
