# Lemma 3.2 (Lemma W) and Lemma 3.3 for one pair: every extension of `Δ_A(λ)` by `∇_A(μ)` splits

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §3.2, Lemma 3.2 and the first sentence of Lemma 3.3:

  **Lemma 3.2 (Lemma W).** Let `X` be a lattice with a sublattice `N` such that `X/N ≅ Δ_A(λ)` and every weight of `N` lies in `[−λ, λ]`. Then the extension splits.

  **Lemma 3.3, first sentence.** For all `λ, μ ≥ 0`, `Ext^1(Δ_A(λ), ∇_A(μ)) = 0`. (Proof: if `μ ≤ λ`, Lemma 3.2; if `μ > λ`, the duality `ι` exchanges the roles and the first case applies.)

This is the ninth piece of stage 1c. The rest of §3.2 (Δ- and ∇-filtrations, lifting modulo 2, Corollary 3.4) is the next piece, C26.

**How the paper's setting is modelled.** Extensions are taken inside DP-lattices: an extension of `Z` by `N` is a short exact sequence `N —f→ X —g→ Z` of DP-lattices (C19 `WeylFilt.ShortExact`), so `X` comes with a basis of weight vectors. The paper's parenthetical remark in Lemma 3.3 — that an extension of `Dist_A`-modules of two lattices is automatically a lattice (Weyl's theorem over `ℚ`) — is not part of this piece. The duality `ι` is the contravariant dual: same basis and weights, `F^{(r)}` and `E^{(r)}` exchanged and transposed.

It reuses:
- piece C18 (`RequestProject/DPLattice/`): `DPLattice`, `DPLattice.IsDP`, `DPLattice.Hop`, `DPLattice.H`, `DPLattice.Hom`, `DPLattice.delta`, `DPLattice.nabla`, `DPLattice.weylWt`, `DPLattice.deltaF`, `DPLattice.deltaE`, `DPLattice.nablaF`, `DPLattice.nablaE`;
- piece C19 (`RequestProject/WeylFilt/`): `WeylFilt.Hom.id`, `WeylFilt.Hom.comp`, `WeylFilt.Hom.ext'`, `WeylFilt.ShortExact`;
- piece C20 (`RequestProject/Doubling/`): `Doubling.Iso`, `Doubling.Iso.ofInverse`.

## Setting

- `A` is a commutative ring. Where it is said, `A` is moreover a domain of characteristic zero (`[IsDomain A] [CharZero A]`); the case of the paper is `A = ℤ_[2]`.
- For DP-lattices `M`, `N` over `A`, a linear map `φ : (M.ι → A) →ₗ[A] (N.ι → A)` is **weight-preserving** if `φ (δ_i) j = 0` whenever `M.wt i ≠ N.wt j`.
- For `w : ℤ`, the **weight projection** `pr w : (M.ι → A) →ₗ[A] (M.ι → A)` keeps the coordinates of weight `w` and sets the others to `0`: `(pr w z) i = if M.wt i = w then z i else 0`. A vector `z` **has weight `w`** if `pr w z = z`.
- The transpose of `φ : (ι → A) →ₗ[A] (κ → A)` (finite `ι`, `κ`) is `trM φ := Matrix.toLin' (LinearMap.toMatrix' φ)ᵀ : (κ → A) →ₗ[A] (ι → A)`; on basis vectors, `trM φ (δ_k) i = φ (δ_i) k`.

## Part P — weights of morphisms and of extensions

**(P1)** If `A` is a domain of characteristic zero, the underlying map of every `f : Hom M N` is weight-preserving. (It commutes with `H`: `(N.wt j − M.wt i) · f(δ_i) j = 0`.)

**(P2)** A weight-preserving `φ` commutes with the weight projections: `φ ∘ pr w = pr w ∘ φ` for every `w`. On every DP-lattice, `F^{(r)} ∘ pr w = pr (w − 2r) ∘ F^{(r)}` and `E^{(r)} ∘ pr w = pr (w + 2r) ∘ E^{(r)}`.

**(P3) Weights of an extension.** Let `f : Hom N X`, `g : Hom X Z` be a short exact sequence with `f.toLin`, `g.toLin` weight-preserving, and `w : ℤ` such that no basis index of `N` and no basis index of `Z` has weight `w`. Then `pr w = 0` on `X`.

## Part D — the contravariant dual

**(D1)** For a DP-lattice `M`, `dual M` has basis `M.ι`, weights `M.wt`, `F^{(r)} := trM (M.Ed r)` and `E^{(r)} := trM (M.Fd r)`; it satisfies `IsDP` ((W), (P0), (P1), (K)). On basis vectors: `(dual M).Fd r (δ_i) j = M.Ed r (δ_j) i` and `(dual M).Ed r (δ_i) j = M.Fd r (δ_j) i`.

**(D2)** For `f : Hom M N`, `dualHom f : Hom (dual N) (dual M)` with underlying map `trM f.toLin`. `dualHom (Hom.id M) = Hom.id (dual M)` and `dualHom (Hom.comp g f) = Hom.comp (dualHom f) (dualHom g)`. If `f.toLin` is weight-preserving, so is `trM f.toLin`.

**(D3)** `dual (dual M) ≅ M`, with both underlying linear maps the identity of `M.ι → A`.

**(D4)** `dual (delta A l)` and `nabla A l` have the same basis `Fin (l + 1)`, the same weights and the same operators (`F^{(r)}`, `E^{(r)}` equal for every `r`); so `dual (delta A l) ≅ nabla A l` with both underlying maps the identity. Likewise `dual (nabla A l) ≅ delta A l`. (Because `deltaMatF l t` is the transpose of `nablaMatE l t` and `deltaMatE l s` the transpose of `nablaMatF l s`.)

**(D5)** Over any commutative ring: if `f : Hom N X`, `g : Hom X Z` is short exact, then `dualHom g : Hom (dual Z) (dual X)`, `dualHom f : Hom (dual X) (dual N)` is short exact.

## Part W — Lemma 3.2 (Lemma W)

Let `l : ℕ` and let `f : Hom N X`, `g : Hom X (delta A l)` be short exact, with `f.toLin`, `g.toLin` weight-preserving and `−l ≤ N.wt i ≤ l` for every `i : N.ι`.

**(W1)** There is `x : X.ι → A` of weight `l` with `g.toLin x = δ_0` (`δ_0 = e_0`, the highest weight vector of `Δ_A(l)`).

**(W2)** For every `x` of weight `l`: `X.Ed s x = 0` for `s ≥ 1`, and `X.Fd r x = 0` for `r > l`.

**(W3)** For `x` as in (W1), the linear map `sW x : (Fin (l + 1) → A) →ₗ[A] (X.ι → A)` with `sW x (δ_r) = X.Fd r x` is a `Hom (delta A l) X`, and `Hom.comp g (sW x) = Hom.id (delta A l)`. The proof uses (K) on `x`: `E^{(s)} F^{(r)} x = C(l − r + s, s) · F^{(r−s)} x` for `s ≤ r`, and `0` for `s > r`.

**(W4) Lemma 3.2.** `∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id (delta A l)`.

**(W5)** If `A` is a domain of characteristic zero, (W4) holds without the weight-preservation hypotheses (by (P1)).

## Part E — Lemma 3.3 for one pair

**(E1) Splitting.** For a short exact sequence `f : Hom N X`, `g : Hom X Z` over any commutative ring: `(∃ s : Hom Z X, Hom.comp g s = Hom.id Z) ↔ (∃ r : Hom X N, Hom.comp r f = Hom.id N)`.

**(E2) Lemma 3.3, first sentence.** For all `l m : ℕ`, every short exact sequence `f : Hom (nabla A m) X`, `g : Hom X (delta A l)` with `f.toLin`, `g.toLin` weight-preserving splits: `∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id _` and `∃ r : Hom X (nabla A m), Hom.comp r f = Hom.id _`.
- If `m ≤ l`: the weights `m − 2t` of `nabla A m` lie in `[−l, l]`, so (W4) applies.
- If `m > l`: apply (D5) to get the short exact sequence `dual (delta A l) → dual X → dual (nabla A m)`, compose with the identity isomorphisms of (D4) to get `nabla A l → dual X → delta A m`, apply (W4) (the weights of `nabla A l` lie in `[−m, m]`), dualize the section back with (D2), (D3), (D4) to a retraction of `f`, and conclude by (E1).

**(E3)** If `A` is a domain of characteristic zero, (E2) holds without the weight-preservation hypotheses.

**(E4) The case of the paper.** For `A = ℤ_[2]` and all `l m : ℕ`, every short exact sequence `nabla ℤ_[2] m → X → delta ℤ_[2] l` splits (both forms of (E2)).

## Proof sketch

(P1): `comm_H` evaluated at `δ_i`, coordinate `j`, gives `(N.wt j : A) f(δ_i) j = (M.wt i : A) f(δ_i) j`, and `N.wt j − M.wt i ≠ 0` is a nonzero integer, so a nonzero element of `A`. (P2): coordinatewise from the definition and from (W) of `IsDP`. (P3): let `y` have weight `w`; `g y = g (pr w y) = pr w (g y) = 0` since `Z` has no basis index of weight `w`; by exactness `y = f n`; then `y = pr w y = f (pr w n) = f 0 = 0`.

(D1): (W) is (W) of `M` read on transposes; (P0), (P1) are the transposes of (P0), (P1) of `M` (transpose reverses composition, `C(a+b, a)` is symmetric in `a, b`); (K) is the transpose of (K) of `M` with `r` and `s` exchanged, using that `H` is diagonal (the binomial coefficient `C(wt + s − r, j)` is read at the weight of the other end, which is shifted by `2(r − s)`; check this carefully on basis vectors, it is the only delicate point). (D3), (D4): transpose twice is the identity; compare the matrices of C18 entrywise. (D5): `g` is onto the free module `Z.ι → A`, so it has an `A`-linear section `σ`; then `ρ := id − σ ∘ g` factors through `f` (by exactness), giving a linear retraction of `f`; transposing, `trM g` is injective, `trM f` is onto (it has the section `trM` of that retraction), and `range (trM g) = ker (trM f)` by the same splitting.

(W1): take `y` with `g y = δ_0` (surjectivity) and `x := pr l y`; `g x = pr l (g y) = δ_0`. (W2): `E^{(s)} x` has weight `l + 2s > l` and `F^{(r)} x` has weight `l − 2r < −l` for `r > l`; every weight of `N` and of `Δ_A(l)` lies in `[−l, l]`, so (P3) gives `0`. (W3): `F^{(t)} F^{(r)} x = C(r + t, t) F^{(r+t)} x` by (P1) of `IsDP`, which is `sW x (F^{(t)} δ_r)` (both `0` when `r + t > l`); (K), extended linearly to `x` (all of whose coordinates have weight `l`), gives `E^{(s)} F^{(r)} x = Σ_j C(l + s − r, j) F^{(r−j)} E^{(s−j)} x`, and by (W2) only `j = s` survives, giving `C(l − r + s, s) F^{(r−s)} x = sW x (E^{(s)} δ_r)`; `H` because `F^{(r)} x` has weight `l − 2r`. Finally `g (sW x δ_r) = g (F^{(r)} x) = F^{(r)} (g x) = F^{(r)} δ_0 = δ_r` (C18: `F^{(r)} e_0 = C(r, r) e_r`), so `g ∘ sW x = id`.

(E1): given a section `s`, `r := ` the unique linear map with `f ∘ r = id − s ∘ g` (exists since `id − s ∘ g` vanishes after `g`, exactness, and `f` is injective); it commutes with the operators because `f`, `s`, `g` do and `f` is injective. Conversely, given `r`, `s := (id − f ∘ r) ∘ σ` for any linear section `σ` of `g`; it does not depend on `σ` (two sections differ by something in `range f`, killed by `id − f ∘ r`), and it commutes with the operators: compare `s ∘ F` and `F ∘ s` after applying the injective map `y ↦ (r y, g y)`.

## What is asked

Formalize and prove every statement above in a new folder `RequestProject/LemmaW/`, namespace `LemmaW`. Reuse the objects listed above; do not redefine them. Every isomorphism with both underlying maps stated. Every docstring names its part of this file. No `sorry`, no new axiom, no `native_decide`. Do not change the folders of C1–C24.
