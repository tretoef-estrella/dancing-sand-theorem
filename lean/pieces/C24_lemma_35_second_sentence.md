# Lemma 3.5, second sentence: `(V ⊗ V ⊗ Φ(N)) ⊗ 𝔽_2 ≅ (Φ(N)^2 ⊕ Φ(V ⊗ N)) ⊗ 𝔽_2`

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §3.3, Lemma 3.5. The first sentence of Lemma 3.5 is piece C22. This piece is the second sentence:

  for every lattice `N`, `(V ⊗ V ⊗ Φ(N)) ⊗ 𝔽_2 ≅ (Φ(N)^2 ⊕ Φ(V ⊗ N)) ⊗ 𝔽_2`.

The paper's proof is the chain
  `(V ⊗ V ⊗ Φ(N)) ⊗ 𝔽_2 ≅ V^{⊗3} ⊗ N̄^{[1]} ≅ (V ⊗ V^{[1]} ⊗ N̄^{[1]}) ⊕ (V ⊗ N̄^{[1]})^2 = (V ⊗ (V ⊗ N̄)^{[1]}) ⊕ (V ⊗ N̄^{[1]})^2`,
which is `(Φ(V ⊗ N) ⊕ Φ(N)^2) ⊗ 𝔽_2`, with `N̄ := N ⊗ 𝔽_2`. It uses Proposition 3.1 (c), base change of `⊗` and `⊕`, and the monoidality of the twist. This is the eighth piece of stage 1c.

It reuses:
- piece C18 (`RequestProject/DPLattice/`): `DPLattice`, `DPLattice.IsDP`, `DPLattice.H`, `DPLattice.Hom`, `DPLattice.V`, `DPLattice.tensorV`, `DPLattice.bvec`, `DPLattice.delta`, `DPLattice.one`;
- piece C19 (`RequestProject/WeylFilt/`): `WeylFilt.Hom.id`, `WeylFilt.Hom.comp`;
- piece C20 (`RequestProject/Doubling/`): `Doubling.OddUnits`, `Doubling.phi`, `Doubling.Iso`, `Doubling.Iso.ofInverse`, `Doubling.Iso.trans`, `Doubling.Iso.symm`;
- piece C21 (`RequestProject/Twist/`): `Twist.bc`, `Twist.baseChange`, `Twist.bcHom`, `Twist.frob`, `Twist.frobOp`, `Twist.frobHom`, `Twist.VIso`, `Twist.tensorIso` (that is, `(tensorV M)^φ ≅ tensorV (M^φ)`), `Twist.prop31Iso`, `Twist.zmod_two_eq_zero`;
- piece C22 (`RequestProject/Lemma35/`): `Lemma35.dsum`, `Lemma35.dsumHom`, `Lemma35.T3`, `Lemma35.D3`, `Lemma35.VV1`, `Lemma35.isoL1`, `Lemma35.isoL2`;
- piece C23 (`RequestProject/Tensor2/`): `Tensor2.tprod`, `Tensor2.kron`, `Tensor2.tensor`, `Tensor2.kronHom`, `Tensor2.tensorIso`, `Tensor2.tensorVIsoTensor`, `Tensor2.assocIso`, `Tensor2.distribRightIso`, `Tensor2.distribLeftIso`, `Tensor2.tensorVHom`, `Tensor2.tensorVIso`, `Tensor2.dsumIso`, `Tensor2.unitLeftIso`, `Tensor2.unitRightIso`.

## Setting

- `A` is a commutative ring with `[IsDomain A] [CharZero A] [Doubling.OddUnits A]` (the setting of C20, C21).
- `B` is a commutative ring with `h2 : (2 : B) = 0`.
- `φ : A →+* B` is a ring homomorphism. The case of the paper is `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod`.

An isomorphism is a `Doubling.Iso`: `Hom`s both ways whose composites are `Hom.id`. When a statement says «by the identity» or «along a bijection», the theorem must state both underlying linear maps. A reindexing along a bijection `e` of bases sends `δ_x` to `δ_{e x}`, like the reindexings of C23.

## Part I — isomorphisms as a category

**(I1)** `Iso.refl M : M ≅ M`, with both underlying maps the identity. `Iso.trans` and `Iso.symm` (C20) compose and invert the underlying maps.

**(I2) Commutativity of `⊕`.** `dsum M N ≅ dsum N M`, along `inl i ↦ inr i`, `inr j ↦ inl j` (`dsumComm`).

**(I3) Associativity of `⊕`.** `dsum (dsum M N) P ≅ dsum M (dsum N P)`, along `inl (inl i) ↦ inl i`, `inl (inr j) ↦ inr (inl j)`, `inr k ↦ inr (inr k)` (`dsumAssoc`).

## Part B — base change of `⊗` and `⊕` (any `φ : A →+* B`)

Here `A`, `B` are any commutative rings and `φ : A →+* B` any ring homomorphism.

**(B1)** `(M ⊗ N)^φ ≅ M^φ ⊗ N^φ`, with both underlying linear maps the identity of `M.ι × N.ι → B`. Both bases are `M.ι × N.ι`, the weights agree, and the operators agree: `((f ⊠ g))^φ = f^φ ⊠ g^φ`, and base change commutes with finite sums.

**(B2)** `(dsum M N)^φ ≅ dsum M^φ N^φ`, with both underlying linear maps the identity of `M.ι ⊕ N.ι → B`.

**(B3)** An isomorphism `u : M ≅ N` gives `bcIso u : M^φ ≅ N^φ`, with underlying maps `bcHom u.hom`, `bcHom u.inv` (C21 (R2) gives identities and composites).

## Part F — the twist is monoidal and additive (`2 = 0` in `B`)

**(F1)** For DP-lattices `M`, `N` over `B`, `frob h2 (M ⊗ N) ≅ frob h2 M ⊗ frob h2 N`, with both underlying linear maps the identity of `M.ι × N.ι → B`.

Reason: the weights are `2(wt i + wt j) = 2 wt i + 2 wt j`. On the left, `F^{(2s)} = Σ_{a=0}^{s} F^{(a)} ⊠ F^{(s−a)}` and `F^{(2s+1)} = 0`. On the right, `F^{(r)} = Σ_{c=0}^{r} frobOp F c ⊠ frobOp F (r − c)`. A term with `c` odd or `r − c` odd is `0`. So for `r = 2s` only `c = 2a` survives and gives `F^{(a)} ⊠ F^{(s−a)}`; for `r` odd every term has an odd index and the sum is `0`. The same holds for `E`.

**(F2)** `frob h2 (dsum M N) ≅ dsum (frob h2 M) (frob h2 N)`, with both underlying linear maps the identity of `M.ι ⊕ N.ι → B`.

**(F3)** An isomorphism `u : M ≅ N` gives `frobIso u : frob h2 M ≅ frob h2 N`, with underlying maps `frobHom u.hom`, `frobHom u.inv` (C21 (T2)).

## Part L — Lemma 3.5, second sentence

**(L4) Over `B`.** For every DP-lattice `X` over `B`:
  `tensorV (tensorV (tensorV X)) ≅ dsum (tensor (VV1 h2) X) (dsum (tensorV X) (tensorV X))`,
that is, `V^{⊗3} ⊗ X ≅ (V ⊗ V^{[1]}) ⊗ X ⊕ (V ⊗ X)^2`.

The isomorphism is the composite of:
- (P3), (P4) of C23, from `V ⊗ (V ⊗ (V ⊗ X))` to `V^{⊗3} ⊗ X`, where `V^{⊗3} = T3 B = tensorV (tensorV (V B))`;
- `tensorIso (isoL1 h2) (Iso.refl X)`, to `D3 B ⊗ X`, where `D3 B = dsum (delta B 3) (dsum (V B) (V B))`;
- (P5) of C23 twice, to `dsum (delta B 3 ⊗ X) (dsum (V B ⊗ X) (V B ⊗ X))`;
- `tensorIso (isoL2 h2) (Iso.refl X)` on the first summand, and (P3) of C23 backwards on the other two.

Its underlying linear map sends `δ_{(a,(b,(c,x)))}` to the image of `h(δ_{(a,(b,c))})` (C22 `hL`) with `x` attached. Here `δ_{inl r}` goes on to `u(e_r)` (C22 `uL`), `δ_{inr (inl e)}` to `δ_{(e,x)}` in the first copy of `V ⊗ X`, and `δ_{inr (inr e)}` to `δ_{(e,x)}` in the second copy. State this formula on basis vectors.

**(L5) Lemma 3.5, second sentence.** In the Setting, for every DP-lattice `N` over `A`:
  `Nonempty (Iso (baseChange φ (tensorV (tensorV (phi N))))
                 (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))))`,
that is, `(V ⊗ V ⊗ Φ(N))^φ ≅ (Φ(N)^2 ⊕ Φ(V ⊗ N))^φ`.

The chain, with `N̄ := N^φ = baseChange φ N` and `X := frob h2 N̄`:
1. `(tensorV (tensorV (phi N)))^φ ≅ tensorV (tensorV ((phi N)^φ))`: `Twist.tensorIso` twice, the second inside `Tensor2.tensorVIso`;
2. `≅ tensorV (tensorV (tensorV X))`: `Twist.prop31Iso` inside `tensorVIso` twice;
3. `≅ dsum (tensor (VV1 h2) X) (dsum (tensorV X) (tensorV X))`: (L4);
4. `tensor (VV1 h2) X ≅ tensorV (frob h2 ((tensorV N)^φ))`. Here `VV1 h2 = tensorV (frob h2 (V B))`. Use:
   - (P3), then (P4): `tensor (tensor (V B) (frob (V B))) X ≅ tensor (V B) (tensor (frob (V B)) X)`;
   - (F1) backwards, then `frobIso` of (P3) backwards: `tensor (frob (V B)) (frob N̄) ≅ frob (tensorV N̄)`;
   - `frobIso` of `Twist.tensorIso` backwards: `≅ frob ((tensorV N)^φ)`;
   - (P3) backwards;
5. `tensorV (frob h2 ((tensorV N)^φ)) ≅ (phi (tensorV N))^φ`: `Twist.prop31Iso` for `tensorV N`, backwards;
6. `tensorV X ≅ (phi N)^φ`: `Twist.prop31Iso`, backwards, on both copies (P7 of C23);
7. `dsum ((phi (tensorV N))^φ) (dsum ((phi N)^φ) ((phi N)^φ)) ≅ dsum (dsum ((phi N)^φ) ((phi N)^φ)) ((phi (tensorV N))^φ)`: (I2);
8. `≅ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))^φ`: (B2) twice, backwards.

State (L5) also with the explicit isomorphism (`lemma35Iso`) and its underlying linear map on basis vectors. In the basis `δ_{(a,(b,(c,i)))}` of the left side (`a, b, c : Fin 2`, `i : N.ι`; the basis of `phi N` is `Fin 2 × N.ι`), the map sends `δ_{(a,(b,(c,i)))}` to `Σ` over the terms of `hL(δ_{(a,(b,c))})`:
- `δ_{inl r}` becomes `δ_{inr (e, (e', i))}`, where `δ_{(e,e')} = uL(e_r)`; the basis of `phi (tensorV N)` is `Fin 2 × (Fin 2 × N.ι)`;
- `δ_{inr (inl e)}` becomes `δ_{inl (inl (e, i))}`;
- `δ_{inr (inr e)}` becomes `δ_{inl (inr (e, i))}`.

**(L6) The case of the paper.** For every DP-lattice `N` over `ℤ_[2]`:
  `Nonempty (Iso (baseChange PadicInt.toZMod (tensorV (tensorV (phi N))))
                 (baseChange PadicInt.toZMod (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))))`.

## Proof sketch

- **(I1)–(I3), (B2), (F2), (F3), (B3).** Identities, reindexings and functoriality, as in C23 (`isoOfReindex`, `Iso.ofDataEquiv`).
- **(B1).** `bc φ (kron f g) = kron (bc φ f) (bc φ g)`: compare matrices entrywise, since `φ` is multiplicative. `bc φ` is additive, so it commutes with `Σ`.
- **(F1).** Split `range (r + 1)` into even and odd `c`; see Part F.
- **(L4), (L5).** Compose the isomorphisms listed with `Iso.trans`, `Iso.symm`, `tensorIso`, `tensorVIso`, `dsumIso`. The formula on basis vectors follows by unfolding: every step except `isoL1` and `isoL2` is the identity or a reindexing.
- **(L6).** `C3_hyp` of C21.
