# Lemma 3.3 for one pair, in the two forms used by the filtration argument: lifting along a surjection with kernel `∇_A(μ)`, and extending along an injection with cokernel `Δ_A(λ)`

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §3.2, Lemma 3.2 and Lemma 3.3:

  **Lemma 3.2 (Lemma W).** Let `X` be a lattice with a sublattice `N` such that `X/N ≅ Δ_A(λ)` and every weight of `N` lies in `[−λ, λ]`. Then the extension splits.

  **Lemma 3.3.** For all `λ, μ ≥ 0`, `Ext^1(Δ_A(λ), ∇_A(μ)) = 0` […]. Consequently, if `M` has a `Δ`-filtration and `N` a `∇`-filtration, then `Ext^1(M, N) = 0` […]. *Proof.* If `μ ≤ λ`, the weights of `∇_A(μ)` lie in `[−μ, μ] ⊆ [−λ, λ]`: Lemma 3.2. If `μ > λ`, the duality `ι` identifies the group with `Ext^1(Δ_A(μ), ∇_A(λ))`, which vanishes by the first case. The long exact sequences of `Ext` along the filtrations give `Ext^1(M, N) = 0`. […]

This is the tenth piece of stage 1c. Piece C25 proved `Ext^1(Δ_A(λ), ∇_A(μ)) = 0` in the form «every short exact sequence `∇_A(μ) → X → Δ_A(λ)` splits». The long exact sequences of `Ext` along the filtrations use the vanishing in two other forms, which are the content of this piece:

- **lifting:** for every short exact sequence `∇_A(μ) → X → Z`, every morphism `Δ_A(λ) → Z` factors through `X`;
- **extension:** for every short exact sequence `Y → X → Δ_A(λ)`, every morphism `Y → ∇_A(μ)` extends to `X`.

Both are proved here for all `λ, μ`, without pullbacks or pushouts, by the construction of Lemma 3.2 and the duality. The filtrations themselves, `Ext^1(M, N) = 0` for filtered `M`, `N`, the lifting modulo 2 and Corollary 3.4 are the next piece, C27.

**How the paper's setting is modelled.** As in C25: an extension is a short exact sequence of DP-lattices (C19 `WeylFilt.ShortExact`), the maps of the sequence are weight-preserving, and the duality `ι` is the contravariant dual of C25.

It reuses:
- piece C18 (`RequestProject/DPLattice/`): `DPLattice`, `DPLattice.IsDP`, `DPLattice.Hom`, `DPLattice.delta`, `DPLattice.nabla`, `DPLattice.weylWt`, `DPLattice.deltaF`, `DPLattice.deltaE`;
- piece C19 (`RequestProject/WeylFilt/`): `WeylFilt.Hom.id`, `WeylFilt.Hom.comp`, `WeylFilt.Hom.ext'`, `WeylFilt.ShortExact`;
- piece C20 (`RequestProject/Doubling/`): `Doubling.Iso`;
- piece C25 (`RequestProject/LemmaW/`, namespace `LemmaW`): `IsWtPres`, `pr`, `HasWt`, `trM`, `dual`, `dualHom`, `isoDualDual`, `isoDualDelta`, `isoDualNabla`, `sW`, `sWHom'`, and the results `P1`, `P2`, `P3`, `D1`–`D5`, `W1`–`W5`, `E1`–`E4` (with their auxiliary lemmas, for instance `K_vec`, `sW_single`, `trM_single_apply`, `trM_comp`, `trM_trM`, `trM_id`, `dualHom_wtPres`, `exists_section`, `exists_retraction_of_section`).

## Setting

- `A` is a commutative ring. Where it is said, `A` is a domain of characteristic zero; the case of the paper is `A = ℤ_[2]`.
- Weight-preserving maps, weight projections `pr w`, «`z` has weight `w`», and the transpose `trM` are those of C25.
- A DP-lattice `K` **has weights in `[a, b]`** if `a ≤ K.wt i ≤ b` for every `i : K.ι`.

## Part L — lifting along a surjection

**(L0)** If `f : Hom N X` is injective with `f.toLin` weight-preserving, and `f.toLin n` has weight `w`, then `n` has weight `w`. (Apply `f` to `pr w n − n`.)

**(L1) Lemma W, lifting form.** Let `l : ℕ`, let `f : Hom N X`, `g : Hom X Z` be short exact with `f.toLin`, `g.toLin` weight-preserving, and let `N` have weights in `[−l, l]`. Then for every `h : Hom (delta A l) Z` with `h.toLin` weight-preserving there is `h' : Hom (delta A l) X` with `Hom.comp g h' = h`. Moreover `h'` can be taken with underlying map `sW x` for some `x : X.ι → A` of weight `l` with `g.toLin x = h.toLin δ_0`.

(C25 (W4) is the case `Z = delta A l`, `h = Hom.id`.)

## Part X — extending along an injection

**(X1) Lemma W, extension form.** Let `l : ℕ`, let `f : Hom Y X`, `g : Hom X (delta A l)` be short exact with `f.toLin`, `g.toLin` weight-preserving, and let `K` be a DP-lattice with weights in `[−l, l]`. Then for every `k : Hom Y K` with `k.toLin` weight-preserving there is `k' : Hom X K` with `Hom.comp k' f = k`.

(A more general statement with `K` of weights in `[−l − 1, l + 1]` is welcome; say so if you prove it.)

## Part B — Lemma 3.3 for one pair, both forms, both cases

**(B1) Lifting.** For all `l m : ℕ`: if `f : Hom (nabla A m) X`, `g : Hom X Z` is short exact with `f.toLin`, `g.toLin` weight-preserving, then every `h : Hom (delta A l) Z` with `h.toLin` weight-preserving lifts: `∃ h' : Hom (delta A l) X, Hom.comp g h' = h`.
- If `m ≤ l`: (L1), since `nabla A m` has weights in `[−m, m] ⊆ [−l, l]`.
- If `m > l`: by (D5) and (D4), `dual Z → dual X → delta A m` (first map `dualHom g`, second map `(isoDualNabla m).hom ∘ dualHom f`) is short exact and weight-preserving, and `k := (isoDualDelta l).hom ∘ dualHom h : Hom (dual Z) (nabla A l)` is weight-preserving; `nabla A l` has weights in `[−l, l] ⊆ [−m, m]`, so (X1) gives `k' : Hom (dual X) (nabla A l)` with `k' ∘ dualHom g = k`; transpose back: `h' := (isoDualDual X).hom ∘ dualHom k' ∘ (isoDualNabla l).inv`, and `g ∘ h' = h` because `trM` reverses composition and `trM ∘ trM = id`.

**(B2) Extension.** For all `l m : ℕ`: if `f : Hom Y X`, `g : Hom X (delta A l)` is short exact with `f.toLin`, `g.toLin` weight-preserving, then every `k : Hom Y (nabla A m)` with `k.toLin` weight-preserving extends: `∃ k' : Hom X (nabla A m), Hom.comp k' f = k`.
- If `m ≤ l`: (X1), since `nabla A m` has weights in `[−m, m] ⊆ [−l, l]`.
- If `m > l`: by (D5) and (D4), `nabla A l → dual X → dual Y` (first map `dualHom g ∘ (isoDualDelta l).inv`, second map `dualHom f`) is short exact and weight-preserving, and `h := dualHom k ∘ (isoDualNabla m).inv : Hom (delta A m) (dual Y)` is weight-preserving; the kernel `nabla A l` has weights in `[−l, l] ⊆ [−m, m]`, so (L1) gives `h' : Hom (delta A m) (dual X)` with `dualHom f ∘ h' = h`; transpose back: `k' := (isoDualDelta m).hom ∘ dualHom h' ∘ (isoDualDual X).inv : Hom X (nabla A m)`, and `k' ∘ f = k`.

**(B3)** If `A` is a domain of characteristic zero, (B1) and (B2) hold without the weight-preservation hypotheses (by C25 (P1)).

**(B4) The case of the paper.** (B1) and (B2) for `A = ℤ_[2]`, all `l m`, no weight hypotheses.

**(B5) Consistency with C25.** (B1) with `Z = delta A l`, `h = Hom.id` gives the section of C25 (E2); (B2) with `Y = nabla A m`, `k = Hom.id` gives its retraction.

## Proof sketch

(L1): `z := h.toLin δ_0` has weight `l` (`h.toLin` is weight-preserving and `δ_0` has weight `l`), `E^{(s)} z = h (E^{(s)} δ_0) = 0` for `s ≥ 1` and `F^{(r)} z = h (F^{(r)} δ_0) = 0` for `r > l` (C18: `E^{(s)} e_0 = 0`, `F^{(r)} e_0 = 0` beyond the top). Take `y` with `g y = z` and `x := pr l y`; then `g x = pr l z = z`. For `s ≥ 1`, `g (E^{(s)} x) = E^{(s)} z = 0`, so `E^{(s)} x = f n`; `E^{(s)} x` has weight `l + 2s`, so by (L0) `n` has weight `l + 2s > l`, hence `n = 0` because `N` has weights in `[−l, l]`. Likewise `F^{(r)} x = 0` for `r > l` (weight `l − 2r < −l`). So C25 `sWHom' x` is a `Hom (delta A l) X`, and `g (sW x δ_r) = g (F^{(r)} x) = F^{(r)} z = h (F^{(r)} δ_0) = h δ_r` (C18: `F^{(r)} e_0 = e_r` for `r ≤ l`).

(X1): by C25 (W1) there is `x` of weight `l` with `g x = δ_0`. Then `g ∘ sW x = id` on `Fin (l + 1) → A` (C18: `F^{(r)} e_0 = e_r`; `g` commutes with `F^{(r)}`), so `v − sW x (g v) ∈ ker g = range f` for every `v`, and since `f` is injective there is a unique linear `ρ : (X.ι → A) →ₗ[A] (Y.ι → A)` with `f ∘ ρ = id − sW x ∘ g`. Put `k' := k ∘ ρ`. Then `ρ ∘ f = id` (because `g ∘ f = 0`), so `k' ∘ f = k`; and `ρ (F^{(r)} x) = 0` for `r ≤ l`. Every `v` is `f (ρ v) + sW x (g v)`, so it suffices to check that `k'` commutes with `F^{(t)}`, `E^{(s)}`, `H` on `range f` (clear, since `k`, `f` are morphisms and `ρ ∘ f = id`) and on the vectors `F^{(r)} x`, `r ≤ l`:
- `F^{(t)} F^{(r)} x = C(r + t, t) F^{(r + t)} x`. If `r + t ≤ l`, `k'` kills it, and `F^{(t)} k'(F^{(r)} x) = 0`. If `r + t > l`, then `g (F^{(r+t)} x) = F^{(r+t)} δ_0 = 0`, so `F^{(r+t)} x = f y₀` with `y₀` of weight `l − 2(r + t) < −l` (by (L0)); `k y₀` has the same weight (`k.toLin` weight-preserving), so `k y₀ = 0` because `K` has weights in `[−l, l]`; and `ρ (f y₀) = y₀`.
- `E^{(s)} F^{(r)} x = Σ_{j ≤ min(r,s)} C(l + s − r, j) F^{(r−j)} E^{(s−j)} x` (C25 `K_vec`, (K) extended to `x`, which has weight `l`). For `j < s`, `g (E^{(s−j)} x) = E^{(s−j)} δ_0 = 0`, so `E^{(s−j)} x = f y_j` with `y_j` of weight `l + 2(s − j) > l`, hence `k y_j = 0`, and `k' (F^{(r−j)} f y_j) = k (F^{(r−j)} y_j) = F^{(r−j)} (k y_j) = 0`. The term `j = s` (present only if `s ≤ r`) is a multiple of `F^{(r−s)} x` with `r − s ≤ l`, killed by `k'`. So `k' (E^{(s)} F^{(r)} x) = 0 = E^{(s)} k' (F^{(r)} x)`.
- `H F^{(r)} x = (l − 2r) F^{(r)} x` (it has weight `l − 2r`), killed by `k'` on both sides.

(B1), (B2): as indicated in Part B; the transposition steps use C25 (D2) (`trM` of a composite), `trM_trM`, `trM_id`, and the identity isomorphisms of (D3), (D4). (B3), (B4): C25 (P1); `ℤ_[2]` is a domain of characteristic zero. (B5): `Hom.id` is weight-preserving.

## What is asked

Formalize and prove every statement above in a new folder `RequestProject/LiftExt/`, namespace `LiftExt`. Reuse the objects listed above; do not redefine them. Every docstring names its part of this file. No `sorry`, no new axiom, no `native_decide`. Do not change the folders of C1–C25.
