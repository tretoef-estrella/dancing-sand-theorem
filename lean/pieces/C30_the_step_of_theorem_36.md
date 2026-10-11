# C30 — The step of Theorem 3.6: V ⊗ V ⊗ Φ(N) ≅ Φ(N)² ⊕ Φ(V ⊗ N) over A, and the kit of isomorphisms

Piece C30 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §3.3, proof of Theorem 3.6, the sentence «both it and `Φ(T(l))^2 ⊕ Φ(V ⊗ T(l))` have `Δ`- and `∇`-filtrations, and their reductions are isomorphic (Lemma 3.5), so they are isomorphic (Corollary 3.4)»). Folder `RequestProject/Step36/`, namespace `Step36`. The induction of Theorem 3.6 itself, with the multiplicities `m_λ(n)`, is the next piece, C31; it needs exactly the isomorphisms proved here.

## Setting (reused, not redefined)

- C18 (`DPLattice`): `DPLattice`, `Hom`, `one`, `V`, `tensorV`, `tensorWt`.
- C19 (`WeylFilt`): `Hom.id`, `Hom.comp`, `Hom.ext'`.
- C20 (`Doubling`): `phi`, `phiWt`, `phiHom`, `Iso`, `Iso.ofInverse`, `Iso.trans`, `Iso.symm`, `Iso.phi`, `D3`, `OddUnits`.
- C21 (`Twist`): `bc`, `baseChange`, `C3_hyp`.
- C22 (`Lemma35`): `dsum`, `dsumHom`, `hL`, `himg`.
- C23 (`Tensor2`): `isoOfReindex`, `dsumIso`, `tensorVIso`, `tensorVIsoTensor`, `unitRightIso`.
- C24 (`Lemma35b`): `Iso.refl`, `dsumComm`, `dsumAssoc`, `lemma35Iso`, `lemma35Iso_single`, `L5img`, `uIdx`.
- C25 (`LemmaW`): `IsWtPres`, `P1`.
- C27 (`Cocycle`): `zeroL`, `HasDeltaFilt`, `HasNablaFilt`.
- C28 (`Lift2`): `H1`, `H2`, `H3`, `OneAddTwoUnit`, `C3`, `isWtPres_inverse`, `Z1`.
- C29 (`Filt`): `T3`.

`A` is a commutative ring with `[IsDomain A] [CharZero A] [OddUnits A]` (the setting of `phi`), `B` a commutative ring with `h2 : (2 : B) = 0`, `φ : A →+* B`. A vector of `M` is `M.ι → A`, `δ_i = Pi.single i 1`.

## Part W — the isomorphism of C24 preserves weights

Over `B` (characteristic `2`) a morphism need not be weight-preserving a priori (`H` sees weights only modulo `2`), so this is checked on the explicit formula of C24 `lemma35Iso_single`.

**(W1)** `IsWtPres (lemma35Iso φ h2 N).hom.toLin` for every DP-lattice `N` over `A`.

*Sketch.* The source basis vector `δ_{(a,(b,(c,i)))}` of `(V ⊗ V ⊗ Φ(N))^φ` has weight `wV a + wV b + 2 N.wt i + wV c` (`wV 0 = 1`, `wV 1 = −1`). By `lemma35Iso_single` its image is `Σ_q hL(δ_{(a,(b,c))})_q · L5img i q`, and the weights of the targets are: `L5img i (inr (inl e))`, `L5img i (inr (inr e))`: `2 N.wt i + wV e`; `L5img i (inl r)` with `uIdx r = (e, e')`: `2 (wV e' + N.wt i) + wV e`. The term `2 N.wt i` is common, so the claim is a finite check on the table `himg` (eight rows): the weights `3, 1, 1, −1, 1, −1, −1, −3` of `(a,b,c) = (0,0,0), (0,0,1), (0,1,0), (0,1,1), (1,0,0), (1,0,1), (1,1,0), (1,1,1)` are those of every term of `himg (a,(b,c))` (for instance `himg (0,(0,1)) = e_1 + b_0`: `e_1 ↦ uIdx 1 = (1,0)`, weight `2·1 − 1 = 1`; `b_0`, weight `1`).

**(W2)** `IsWtPres (lemma35Iso φ h2 N).inv.toLin` (C28 `isWtPres_inverse`, from (W1) and the two composites of the `Iso`).

## Part A — the step over A

**(A1)** Assume `H1 φ`, `H2 φ`, `H3 A`, `OneAddTwoUnit A`, `h2 : (2 : B) = 0`. For every DP-lattice `N` over `A` with `HasDeltaFilt N` and `HasNablaFilt N` there is
  `e : Iso (tensorV (tensorV (phi N))) (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))`
with `e.hom.toLin`, `e.inv.toLin` weight-preserving, `bc φ e.hom.toLin = (lemma35Iso φ h2 N).hom.toLin` and `bc φ e.inv.toLin = (lemma35Iso φ h2 N).inv.toLin`.

*Proof.* C29 (T3) gives both filtrations of both lattices; (W1), (W2); then C28 (C3) with `ē = lemma35Iso φ h2 N`.

## Part K — the kit of isomorphisms for the induction

All isomorphisms below are `Doubling.Iso`; over `A` (a domain of characteristic `0`) their maps are weight-preserving by C25 (P1), which may be stated or not.

**(K1)** `tensorV (one A) ≅ V A` and `phi (one A) ≅ V A` (C23 `tensorVIsoTensor`, `unitRightIso`; C20 `D3`); hence `tensorV (one A) ≅ phi (one A)`.

**(K2)** `phi` is additive: `phi (dsum M N) ≅ dsum (phi M) (phi N)`, by the identity on the reindexing `Fin 2 × (M.ι ⊕ N.ι) ≃ (Fin 2 × M.ι) ⊕ (Fin 2 × N.ι)` (C23 `isoOfReindex`; the operators of `phi` act slotwise, and `dsum` is blockwise). State the image of every basis vector.

**(K3)** `dsum M (zeroL A) ≅ M` and `dsum (zeroL A) M ≅ M`; `tensorV (zeroL A) ≅ zeroL A`; `phi (zeroL A) ≅ zeroL A`.

**(K4)** Finite direct sums. Define `dsumList : List (DPLattice A) → DPLattice A` by `dsumList [] = zeroL A`, `dsumList (X :: L) = dsum X (dsumList L)`, with these equations as theorems. Then:
- (a) `dsumList (L₁ ++ L₂) ≅ dsum (dsumList L₁) (dsumList L₂)`;
- (b) if `L`, `L'` have the same length and `Iso (L.get k) (L'.get k)` for every `k` (or: a `List.Forall₂` of nonempty isomorphisms), then `dsumList L ≅ dsumList L'` (stated with `Nonempty` if that is easier);
- (c) `tensorV (dsumList L) ≅ dsumList (L.map tensorV)` (C23 distributivity through `tensorVIsoTensor`);
- (d) `phi (dsumList L) ≅ dsumList (L.map phi)` (from (K2), (K3));
- (e) `dsumList [X] ≅ X`.

## Part Z — the case of the paper

**(Z1)** (W1), (W2) and (A1) for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod` (the hypotheses by C28 (Z1) and C21 `C3_hyp`).

## Notes

- Nothing is cited. (W1) is a finite check on the table of C22; (A1) assembles C24, C28, C29; Part K is reindexing.
- Brute force (`chkC30.py`): the weight check of (W1) on the eight rows of `himg` with the target weights read off `L5img` and `uIdx`, for `N.wt i` from `−4` to `4`; the explicit matrix of `lemma35Iso` built from `himg`, `uIdx`, `L5img` for `N ∈ {one, V, Δ(2)}` over `𝔽_2` is weight-preserving, invertible, and commutes with every `F^(r)`, `E^(r)` of the two base-changed lattices; (A1) is checked by lifting it with the procedure of C28 (L2) over `ℤ_(2)` and verifying that the lift and the lift of the inverse compose to matrices `≡ 1 (mod 2)` with odd determinant; (K2) the reindexed identity commutes with the operators of `phi (dsum M N)` and `dsum (phi M) (phi N)`. Controls: a deliberately wrong row of `himg` (`e_1 ↦ e_2`) is not weight-preserving; a wrong reindexing in (K2) does not commute.
