# The tensor product of DP-lattices (toward Lemma 3.5, second sentence)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §3.3, Lemma 3.5. Its second sentence uses `V^{⊗3} ⊗ N̄^{[1]}`, `V ⊗ V^{[1]} ⊗ N̄^{[1]}` and the monoidality of the twist. These need the tensor product of two DP-lattices, with the coproduct of the divided powers. This is the seventh piece of stage 1c. The next piece (C24) assembles the second sentence of Lemma 3.5.

It reuses:
- piece C18 (`RequestProject/DPLattice/`): `DPLattice`, `DPLattice.IsDP`, `DPLattice.H`, `DPLattice.Hom`, `DPLattice.V`, `DPLattice.tensorV`, `DPLattice.bvec`, `DPLattice.slice`, `DPLattice.delta`, `DPLattice.nabla`, `DPLattice.one`;
- piece C19 (`RequestProject/WeylFilt/`): `WeylFilt.Hom.id`, `WeylFilt.Hom.comp`;
- piece C20 (`RequestProject/Doubling/`): `Doubling.Iso`, `Doubling.Iso.ofInverse`, `Doubling.Iso.trans`, `Doubling.Iso.symm`;
- piece C22 (`RequestProject/Lemma35/`): `Lemma35.dsum`, `Lemma35.dsumHom`.

## Setting

`A` is any commutative ring. A vector of a DP-lattice `M` is `M.ι → A`, and the basis vector at `i` is `δ_i = Pi.single i 1`.

For linear endomorphisms `f` of `ι → A` and `g` of `κ → A`, write `f ⊠ g` for the linear endomorphism of `ι × κ → A` with
  `(f ⊠ g)(δ_{(i,j)}) (i', j') = f(δ_i)(i') · g(δ_j)(j')`
(the Kronecker product of the matrices). The same formula defines `f ⊠ g` for linear maps `f : (ι → A) → (ι' → A)` and `g : (κ → A) → (κ' → A)`, with values in `ι' × κ' → A`.

## Part P — the tensor product

**(P1) The tensor product.** For DP-lattices `M`, `N` over `A`, `M ⊗ N` (`tensor M N`) has:
- the basis `M.ι × N.ι`;
- the weights `wt(i, j) = M.wt i + N.wt j`;
- `F^{(r)} := Σ_{a=0}^{r} M.Fd a ⊠ N.Fd (r − a)`;
- `E^{(r)} := Σ_{a=0}^{r} M.Ed a ⊠ N.Ed (r − a)`.

That is, `F^{(r)}(m ⊗ n) = Σ_{a+b=r} F^{(a)} m ⊗ F^{(b)} n`, and likewise for `E`.

`M ⊗ N` satisfies `IsDP`: (W), (P0), (P1) and (K). So `M ⊗ N : DPLattice A`.

**(P2) Morphisms.** For `f : Hom M M'` and `g : Hom N N'`, the linear map `f ⊠ g` is a `Hom (M ⊗ N) (M' ⊗ N')`. Moreover:
- `Hom.id M ⊠ Hom.id N = Hom.id (M ⊗ N)`;
- `(f ∘ f') ⊠ (g ∘ g') = (f ⊠ g) ∘ (f' ⊠ g')`;
- consequently, isomorphisms `M ≅ M'` and `N ≅ N'` give an isomorphism `M ⊗ N ≅ M' ⊗ N'` (`tensorIso`).

**(P3) `V ⊗ −` is a tensor product.** For every DP-lattice `M`, `tensorV M ≅ V A ⊗ M`. The underlying linear maps, both ways, are the identity of `Fin 2 × M.ι → A`. Both bases are `Fin 2 × M.ι` and the weights agree.

**(P4) Associativity.** For DP-lattices `M`, `N`, `P`, `(M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)`. The underlying linear maps are the reindexing along `((i, j), k) ↦ (i, (j, k))` and its inverse.

**(P5) Distributivity over the direct sum.** For DP-lattices `M`, `N`, `P`:
- `dsum M N ⊗ P ≅ dsum (M ⊗ P) (N ⊗ P)`, along `(inl i, k) ↦ inl (i, k)` and `(inr j, k) ↦ inr (j, k)`;
- `M ⊗ dsum N P ≅ dsum (M ⊗ N) (M ⊗ P)`, along `(i, inl j) ↦ inl (i, j)` and `(i, inr k) ↦ inr (i, k)`.

**(P6) `V ⊗ −` on morphisms.** For `f : Hom M N`, the linear map `id ⊠ f` of `Fin 2 × M.ι → A` (that is, `bvec e m ↦ bvec e (f m)`) is a `Hom (tensorV M) (tensorV N)`. It sends `Hom.id` to `Hom.id` and composites to composites. Consequently, an isomorphism `M ≅ N` gives `tensorV M ≅ tensorV N` (`tensorVIso`).

**(P7) Direct sum of isomorphisms.** Isomorphisms `M ≅ M'` and `N ≅ N'` give `dsum M N ≅ dsum M' N'` (`dsumIso`), with underlying maps `dsumHom`.

**(P8) The unit.** `one A ⊗ M ≅ M` and `M ⊗ one A ≅ M`, along `((), i) ↦ i` and `(i, ()) ↦ i`.

## Proof sketch

- **(P1), (W) and (P0).** Weights add; `F^{(0)} = 1 ⊠ 1 = 1`.
- **(P1), (P1).** `F^{(a)} F^{(b)}` on `δ_i ⊗ δ_j` is `Σ_{c, d} F^{(c)}F^{(c')} δ_i ⊗ F^{(d)}F^{(d')} δ_j`. By (P1) of `M` and `N` it equals `Σ C(c+c', c) C(d+d', d) F^{(c+c')} δ_i ⊗ F^{(d+d')} δ_j`. Vandermonde's identity, `Σ_{c+d=a} C(x, c) C(y, d) = C(x + y, a)` with `x = c + c'` and `y = d + d'`, gives `C(a + b, a) F^{(a+b)}`.
- **(P1), (K).** Expand `E^{(s)} F^{(r)}(δ_i ⊗ δ_j) = Σ_{c+d=s} Σ_{a+b=r} E^{(c)}F^{(a)} δ_i ⊗ E^{(d)}F^{(b)} δ_j`, and expand each factor by (K) of `M` and of `N`. Collect the terms `F^{(a')}E^{(c')} δ_i ⊗ F^{(b')}E^{(d')} δ_j` with `a' + b' = r − j` and `c' + d' = s − j`. The coefficient is `Σ_{j_1 + j_2 = j} C(w_i + c' − a', j_1) C(w_j + d' − b', j_2)`. By Vandermonde over `ℤ` (`Ring.add_choose_eq`, negative tops included) this is `C(w_i + w_j + s − r, j)`, which is (K) for `M ⊗ N`.
- **(P2).** `(f ⊠ g)(F^{(a)} ⊠ F^{(b)}) = (f F^{(a)}) ⊠ (g F^{(b)}) = (F^{(a)} f) ⊠ (F^{(b)} g)`; sum over `a + b = r`. For `H`, weights add.
- **(P3).** On `V`, `F^{(a)} = 0` for `a ≥ 2`. So `F^{(r)}(b_0 m) = b_0 F^{(r)} m + b_1 F^{(r−1)} m` and `F^{(r)}(b_1 m) = b_1 F^{(r)} m`, which are the formulas of `tensorV` (C18, `tensorFd_bvec0`, …). The same holds for `E`.
- **(P4).** Both sides are `Σ_{a+b+c=r} F^{(a)} ⊠ F^{(b)} ⊠ F^{(c)}`.
- **(P5).** Blockwise.
- **(P6).** By (P2) and (P3), or directly from the formulas of `tensorV`.
