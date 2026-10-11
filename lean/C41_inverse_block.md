# C41 — Lemma 10.8: the inverse block, as a lift identity along the dance (paper v8 §10.4)

*Lean piece C41 of the Dancing Sand Theorem. Grepy Escribano, 9 October 2026. Folder `RequestProject/InvBlock/`, namespace `InvBlock`. Do not change any earlier file.*

Lemma 10.8 of the paper: if `Ξ` is invertible on `T(l) ⊗ ℚ` and its dance is clean, then for every level `h`, `G_h^{−1} = 2^h · out_h ∘ Ξ^{−1} ∘ in_h`, where `in_h` (coordinates) and `out_h` (sources) depend only on the word of `l`. This piece proves it in an inverse-free form, over the same ring `A` as C40c–C40d, and then derives the inverse form over a field. The floors of `in_h` and `out_h` (the offsets `o_D`) and Corollary 10.9 go to C42.

**The idea, one step.** For a clean twist move with witness `Q` (C40b `CleanStep`), and C40c (T1): `sysAct (phi N) G (pack (u, v)) = pack (B u + Dd v, P u + C v)` with `P = twP G`, `C = twC G`, `B = twB G`, `Dd = twD G`. Put `u := − (Q * C) v`. Then the `b_1`-component is `P u + C v = 0` and the `b_0`-component is `(Dd − B Q C) v = 2 G' v`. So
  `sysAct (phi N) G ∘ lift = inj₀ ∘ (2 • sysAct N G')`,  `lift v := pack (−sysAct N (Q * twC G) v, v)`,  `inj₀ x := pack (x, 0)`,
and `out₁ ∘ lift = id` with `out₁ w := (pack.symm w).2`. A split move is the same after C40c (T2) (`vpack`) and the relabelling C40c (A3).

## Setting (reuse; do not redefine)

- C13 `Dance.slots`, `Dance.splitIso`; C18 `DPLattice`, `DPLattice.one`; C29 `Filt.T` (`T_zero`, `T_odd`, `T_even`); C32 `Families.ds` (`ds_zero`, `ds_odd`, `ds_even`).
- C40 `FormalOps.Bf`, `act`; C40b `FormalDance.MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `DanceRel`, `finalM`; C40c `FormalAct.sysAct`, `pack`, `vpack`, `unitEquiv`, `N1`, `N2`, `A1`, `A2` (`sysAct_mul`, `sysAct_one`, `sysAct_sub`, `sysAct_smul`), `A3_conj`, `A4_apply`, `T1`, `T2`, `pivotEquiv`, `schur_eq`; C40d `FormalProp.Q0` and the induction pattern of `FormalProp.Q1_aux` (on the list `Families.ds l`, for all `r`, `G`, `Gk`, `B ≥ l + 1` at once).

`A` is a commutative ring with `[IsDomain A] [CharZero A] [OddUnits A]`. Write `k := (Families.ds l).length`, `m := Dance.mCount (Families.ds l)`, `ns := Dance.slots (Families.ds l) r`. The action on `T A l` is taken with top `W = (l : ℤ)` and any `B ≥ l + 1`.

## Statements to prove

**Definitions (new).**
- `inH (l r : ℕ) : (Fin (Dance.slots (Families.ds l) r) → A) →ₗ[A] (Fin r → (T A l).ι → A)` and `outH (l r : ℕ) : (Fin r → (T A l).ι → A) →ₗ[A] (Fin (Dance.slots (Families.ds l) r) → A)`, by recursion along `l` as in `Q1_aux`: at `l = 0` the identity through `unitEquiv`; at a twist step `inH = inj₀ ∘ inH'` and `outH = outH' ∘ out₁` (`inj₀ x = pack (x, 0)`, `out₁ w = (pack.symm w).2`); at a split step the same through `vpack` and the relabelling `j ↦ ofLex ((Dance.splitIso r).symm j)` of C40c (A3). **They depend only on `l` and `r`, never on a system.**

**(V1) One twist move.** For `N : DPLattice A`, `W`, `BN`, `B`, `B'` with `htop : ∀ i, N.wt i ≤ W ∧ Even (W − N.wt i)`, `hnil : ∀ s ≥ BN, N.Fd s = 0`, `2 * BN ≤ B`, `BN ≤ B'`, `1 ≤ B'`, and `G G' Q : Matrix n n (Bf A)` with `MAgree (twP G * Q) 1`, `MAgree (Q * twP G) 1`, `MAgree (twD G − twB G * Q * twC G) ((2 : A) • G')`: with `lift v := pack (−sysAct N W B' (Q * twC G) v, v)`,
  `sysAct (phi N) (2 * W + 1) B G (lift v) = pack ((2 : A) • sysAct N W B' G' v, 0)`  and  `(pack.symm (lift v)).2 = v`  for every `v`.

**(V2) One split move.** Under the hypotheses of C40c (S2) (`2 * BN + 1 ≤ B`, `BN ≤ B'`, `1 ≤ B'`) and a witness `Q` of `CleanStep (vsplit G) G''` as in (V1): the same two identities for `sysAct (tensorV (phi N)) (2 * W + 2) B G` composed with `vpack`, with `lift` built from `vsplit G` on `phi N`.

**(V3) Lemma 10.8, lift form.** For all `l r : ℕ`, `G : Matrix (Fin r) (Fin r) (Bf A)`, `Gk : Matrix (Fin ns) (Fin ns) (Bf A)` with `DanceRel (Families.ds l) r G Gk`, and every `B ≥ l + 1`: there is a linear map `L : (Fin ns → A) →ₗ[A] (Fin r → (T A l).ι → A)` with
  `sysAct (T A l) (l : ℤ) B G ∘ₗ L = (2 : A) ^ k • (inH l r ∘ₗ Matrix.mulVecLin (finalM Gk))`  and  `outH l r ∘ₗ L = LinearMap.id`.

**(V4) Corollary of (V3), over the same `A`.** In the setting of (V3), if `sysAct (T A l) (l : ℤ) B G` is injective, then `Matrix.mulVecLin (finalM Gk)` is injective.

**(V5) Lemma 10.8, inverse form, over a field.** Let `K` be a field with `[CharZero K] [OddUnits K]`. In the setting of (V3) over `K`, let `e : (Fin r → (T K l).ι → K) ≃ₗ[K] (Fin r → (T K l).ι → K)` with `(e : _ →ₗ[K] _) = sysAct (T K l) (l : ℤ) B G`. Then `IsUnit (finalM Gk).det` and
  `Matrix.mulVecLin ((finalM Gk)⁻¹) = (2 : K) ^ k • (outH l r ∘ₗ (e.symm : _ →ₗ[K] _) ∘ₗ inH l r)`.
(This is the paper's `G_k^{−1} = 2^k · out ∘ Ξ^{−1} ∘ in` at the last level, the one Corollary 10.9 uses.)

## Proof sketch
- (V1): C40c (T1) with `u = −sysAct (Q * twC G) v`; `sysAct_mul` and (A1) give `sysAct (twP G) (sysAct (Q * twC G) v) = sysAct (twC G) v`; the `b_0`-component is `sysAct (twD G − twB G * Q * twC G) v = (2 : A) • sysAct G' v` (C40c `schur_eq`, or `sysAct_mul`, `sysAct_sub`, (A1), `sysAct_smul`). The second identity is `pack.symm_apply_apply`.
- (V2): C40c (T2) turns the action on `tensorV (phi N)` into the action of `vsplit G` on `phi N` through `vpack`; then (V1) with `n × Fin 2`.
- (V3): induction as in `FormalProp.Q1_aux` (on `Families.ds l`, for all `r`, `G`, `Gk`, `B ≥ l + 1`). `l = 0`: `L = inH 0 r` (through `unitEquiv`), by (A1) and (A4_apply). Twist step: `L = lift ∘ L'` with `L'` from the induction hypothesis on `T A l'`; then `sysAct G ∘ lift ∘ L' = inj₀ ∘ 2 • sysAct G' ∘ L' = 2 • inj₀ ∘ 2^{k−1} • inH' ∘ M = 2^k • inH ∘ M`. Split step: the same with (V2) and the relabelling (A3_conj).
- (V4): if `M z = 0` then `sysAct G (L z) = 0`, so `L z = 0`, so `z = outH (L z) = 0`.
- (V5): by (V4) `finalM Gk` is injective, hence invertible over a field (square matrix). Put `z := M⁻¹ y`; (V3) gives `sysAct G (L z) = 2^k inH y`, so `L z = 2^k e.symm (inH y)` and `z = outH (L z) = 2^k outH (e.symm (inH y))`.

## Checks done before sending
- Brute force `chkC41.py` (definitions as in `chkC40c.py`: independent lattice model of `T(λ)`, `Φ`, `V ⊗ −` over `ℚ`, the nested basis `(e, j)` of `Φ` and `(a, (e, j))` of `V ⊗ Φ`; the data dance by C11 `pT`, `κT` and C12 `pSp`, `κSp`). At every level of the dance: the twist blocks read off the matrix of the action, the Schur complement `Dd − B P^{−1} C` equals `2 ·` the action of the next system, and the lift `(−P^{−1} C L', L')` is built. Then `G L = 2^k I M` and `O L = 1`: `l ≤ 7`, sizes 1–3 (`r · dim ≤ 48`), two random data each (the lift form holds also for systems that are not invertible); the inverse form `M^{−1} = 2^k O G^{−1} I` for data with `p(f) ≠ 0` everywhere; `σ^{(α)}_i` with `i = 1, 2, 5`, `α = 1, 2, 3`, `l ≤ 7`. **334 checks, 0 failures.** `logs/chkC41.log`.
- Controls (all five fire): `I` reading the `b_1`-slots; `O` reading the `b_0`-slots; the lift without the correction `−P^{−1} C`; the split slots ordered `(a, s)` instead of `(s, a)`; the factor `2^{k−1}` instead of `2^k`.
- Two errors of my first run, both mine and both in the test, not in the statements: random data with `p(f) = 0` made the system non-invertible, so the inverse form had nothing to check (23 cells); and the scale control used `2^2` at `l = 5`, where `k = 2`, so it could not fire. Both repaired before sending. A first draft of (V4) carried a false clause (`outH ∘ inH = id`; in fact `inH` writes the `b_0`-slots and `outH` reads the `b_1`-slots); it was removed before sending.

## Notes
- §10.4 is split in three: C41 (Lemma 10.8, this piece), C42 (the floors of `inH`, `outH` and Corollary 10.9), C43 (Lemmas 10.10, 10.11 and Theorem 10.12).
