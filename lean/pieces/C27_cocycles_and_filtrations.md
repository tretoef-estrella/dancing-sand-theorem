# Lemma 3.3, second sentence: `Ext^1(M, N) = 0` when `M` has a `Δ`-filtration and `N` a `∇`-filtration — through explicit cocycles

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §3.2, Lemma 3.3:

  **Lemma 3.3.** For all `λ, μ ≥ 0`, `Ext^1(Δ_A(λ), ∇_A(μ)) = 0` […]. Consequently, if `M` has a `Δ`-filtration and `N` a `∇`-filtration, then `Ext^1(M, N) = 0`, and the reduction map `Hom_{Dist_A}(M, N) → Hom_{Dist_{𝔽_2}}(M ⊗ 𝔽_2, N ⊗ 𝔽_2)` is onto.
  *Proof.* […] The long exact sequences of `Ext` along the filtrations give `Ext^1(M, N) = 0`. […]

This is the eleventh piece of stage 1c. It proves `Ext^1(M, N) = 0` for `Δ`-filtered `M` and `∇`-filtered `N`. The reduction map, the lifting modulo 2 and Corollary 3.4 are the next piece, C28.

**How the paper's setting is modelled, and why cocycles.** As in C25–C26, extensions are short exact sequences of DP-lattices with weight-preserving maps. The paper's «long exact sequences of `Ext`» would need sub-lattices, quotients and pullbacks of DP-lattices, each with a new basis of weight vectors. Instead, every extension of `M` by `N` is written, up to isomorphism, as a **glued lattice** on the basis `N.ι ⊕ M.ι` with block upper-triangular operators; the upper-right blocks form a **cocycle** `c`; the extension splits exactly when `c` is a **coboundary**. Then each step of the long exact sequences is linear algebra on cocycles, with no new lattice built except the glued ones. (Piece C26 is not needed on this route; it stays as proved.)

It reuses:
- piece C18 (`RequestProject/DPLattice/`): `DPLattice`, `DPLattice.IsDP` (fields `W_F`, `W_E`, `P0_F`, `P0_E`, `P1_F`, `P1_E`, `K`), `DPLattice.Hom`, `DPLattice.delta`, `DPLattice.nabla`, `DPLattice.weylWt`;
- piece C19 (`RequestProject/WeylFilt/`): `WeylFilt.Hom.id`, `WeylFilt.Hom.comp`, `WeylFilt.Hom.ext'`, `WeylFilt.ShortExact`;
- piece C20 (`RequestProject/Doubling/`): `Doubling.Iso`;
- piece C25 (`RequestProject/LemmaW/`, namespace `LemmaW`): `IsWtPres`, `pr`, `HasWt`, the results `P1`, `P2`, `E1`, `E2`, `E3` and their auxiliary lemmas (for instance `exists_section`, `exists_retraction_of_section`).

## Setting

- `A` is a commutative ring; where it is said, a domain of characteristic zero; the case of the paper is `A = ℤ_[2]`.
- Weight-preserving linear maps and `pr w` are those of C25. For DP-lattices `M`, `N`, write `Lin(M, N) := (M.ι → A) →ₗ[A] (N.ι → A)`.
- A vector `z : N.ι ⊕ M.ι → A` is written `z = (u, v)` with `u := z ∘ Sum.inl`, `v := z ∘ Sum.inr`.

## Part G — glued lattices, cocycles, coboundaries

**(G0) The zero lattice.** `zeroL A` has basis `Empty`; it is a DP-lattice.

**(G1) Glued data.** For DP-lattices `M`, `N` and a pair `c = (cF, cE)` of families `cF r, cE r : Lin(M, N)` (`r : ℕ`), the glued data on the basis `N.ι ⊕ M.ι` have weights `Sum.elim N.wt M.wt` and operators
  `F^{(r)} (u, v) := (N.Fd r u + cF r v, M.Fd r v)`,  `E^{(r)} (u, v) := (N.Ed r u + cE r v, M.Ed r v)`.
`c` is a **cocycle from `M` to `N`** if these data satisfy `IsDP`. For a cocycle, `glue M N c : DPLattice A` is the DP-lattice they define.

**(G2) Cocycle equations.** `c` is a cocycle iff all of:
- (W) `cF r (δ_i) j = 0` unless `N.wt j = M.wt i − 2r`, and `cE r (δ_i) j = 0` unless `N.wt j = M.wt i + 2r`;
- (P0) `cF 0 = 0`, `cE 0 = 0`;
- (P1) `N.Fd a ∘ cF b + cF a ∘ M.Fd b = C(a + b, a) · cF (a + b)`, and the same for `E`;
- (K) for every `i : M.ι` and `r, s`: `N.Ed s (cF r δ_i) + cE s (M.Fd r δ_i) = Σ_{j ≤ min(r,s)} C(M.wt i + s − r, j) · (N.Fd (r−j) (cE (s−j) δ_i) + cF (r−j) (M.Ed (s−j) δ_i))`.
(These are the conditions of `IsDP` on the glued data at the basis vectors `δ_{inr i}`, upper component; at `δ_{inl j}` and in the lower component they are those of `N` and of `M`.) In particular cocycles form an `A`-submodule of the pairs of families.

**(G3) The extension.** For a cocycle `c`: `incl : Hom N (glue M N c)`, `u ↦ (u, 0)`, and `proj : Hom (glue M N c) M`, `(u, v) ↦ v`, are morphisms, weight-preserving, and `ShortExact incl proj`.

**(G4) Coboundaries.** For a weight-preserving `ψ : Lin(M, N)`, `dψ := (r ↦ ψ ∘ M.Fd r − N.Fd r ∘ ψ, r ↦ ψ ∘ M.Ed r − N.Ed r ∘ ψ)` is a cocycle. A cocycle is a **coboundary** if it is `dψ` for a weight-preserving `ψ`.

**(G5) Splitting.** For a cocycle `c`, the following are equivalent: (i) `c` is a coboundary; (ii) `proj` has a section in `Hom`; (iii) `incl` has a retraction in `Hom`. For (i) ⇒ (ii) the section is `v ↦ (ψ v, v)`. For (ii) ⇒ (i): a section is `v ↦ (ψ' v, v)` with `ψ'` commuting with the operators up to `c`; its weight-diagonal part `ψ := Σ_w pr w ∘ ψ' ∘ pr w` is weight-preserving and `dψ = c` (compare weight components; over a general ring `ψ'` itself need not be weight-preserving). (ii) ⇔ (iii) is C25 (E1).

**(G6) Change of the ends.**
- (a) If `c` is a cocycle from `M` to `N` and `i : Hom M' M`, `j : Hom N N'` have weight-preserving underlying maps, then `c ∘ i := (cF r ∘ i, cE r ∘ i)` is a cocycle from `M'` to `N`, and `j ∘ c` one from `M` to `N'`. `d(ψ ∘ i) = (dψ) ∘ i` and `d(j ∘ ψ) = j ∘ dψ` for weight-preserving `ψ`.
- (b) If `p : Hom M M''` is surjective with `p.toLin` weight-preserving and `c'' ∘ p` is a cocycle from `M` to `N`, then `c''` is a cocycle from `M''` to `N`.
- (c) If `a : Hom N' N` is injective with `a.toLin` weight-preserving and `a ∘ c'` is a cocycle from `M` to `N`, then `c'` is a cocycle from `M` to `N'`.

**(G7) Every extension is glued.** Let `f : Hom N X`, `g : Hom X M` be short exact with `f.toLin`, `g.toLin` weight-preserving. Then there are a weight-preserving linear section `σ` of `g` and a cocycle `c` from `M` to `N` (namely `cF r = ρ ∘ X.Fd r ∘ σ`, `cE r = ρ ∘ X.Ed r ∘ σ`, where `ρ` is the linear retraction of `f` with `f ∘ ρ = id − σ ∘ g`) and an isomorphism `θ : X ≅ glue M N c` (underlying map `x ↦ (ρ x, g x)`, inverse `(u, v) ↦ f u + σ v`) with `θ ∘ f = incl` and `proj ∘ θ = g`. Consequently, if every cocycle from `M` to `N` is a coboundary, every such sequence splits (`g` has a section and `f` a retraction in `Hom`).

## Part F — filtrations

**(F1)** `HasDeltaFilt : DPLattice A → Prop` is the inductive predicate: (base) if `M.ι` is empty, `HasDeltaFilt M`; (step) if `f : Hom M' M`, `g : Hom M (delta A l)` are short exact with `f.toLin`, `g.toLin` weight-preserving and `HasDeltaFilt M'`, then `HasDeltaFilt M`.
`HasNablaFilt : DPLattice A → Prop`: (base) if `N.ι` is empty; (step) if `f : Hom (nabla A m) N`, `g : Hom N N'` are short exact with `f.toLin`, `g.toLin` weight-preserving and `HasNablaFilt N'`, then `HasNablaFilt N`.
(The paper's filtration is a chain of sublattices with subquotients `Δ_A(λ_k)`; the predicate says that such a chain exists, read from the top for `Δ` and from the bottom for `∇`.)

**(F2)** `HasDeltaFilt (delta A l)` and `HasNablaFilt (nabla A m)` (one step from `zeroL A`).

## Part V — vanishing

**(V1) One pair.** Every cocycle from `delta A l` to `nabla A m` is a coboundary, for all `l m`. (By (G3), (G5) and C25 (E2).)

**(V2) Induction on `M`.** Let `f : Hom M' M`, `g : Hom M (delta A l)` be short exact, weight-preserving, and let `N` be such that every cocycle from `M'` to `N` and every cocycle from `delta A l` to `N` is a coboundary. Then every cocycle from `M` to `N` is a coboundary.
*Proof.* Choose a weight-preserving linear section `σ` of `g` and the retraction `r` of `f` with `f ∘ r = id − σ ∘ g` (`r` is weight-preserving because `f` is injective and weight-preserving). `c ∘ f = dψ'`; put `ψ₀ := ψ' ∘ r`. Then `(c − dψ₀) ∘ f = 0`, so `c − dψ₀ = c'' ∘ g` with `c'' := (c − dψ₀) ∘ σ`, a cocycle from `delta A l` to `N` by (G6)(b); `c'' = dψ''`; so `c = d(ψ₀ + ψ'' ∘ g)`.

**(V3) Induction on `N`.** Let `f : Hom (nabla A m) N`, `g : Hom N N'` be short exact, weight-preserving, and let `M` be such that every cocycle from `M` to `nabla A m` and every cocycle from `M` to `N'` is a coboundary. Then every cocycle from `M` to `N` is a coboundary.
*Proof.* `g ∘ c = dψ'` with `ψ' : Lin(M, N')`; lift it to a weight-preserving `ψ̃ : Lin(M, N)` with `g ∘ ψ̃ = ψ'` (lift weight by weight). Then `g ∘ (c − dψ̃) = 0`, so `c − dψ̃ = f ∘ c'` (since `range f = ker g` and `f` is injective), `c'` a cocycle from `M` to `nabla A m` by (G6)(c); `c' = dψ''`; so `c = d(ψ̃ + f ∘ ψ'')`.

**(V4) Lemma 3.3, second sentence.** If `HasDeltaFilt M` and `HasNablaFilt N`, then every cocycle from `M` to `N` is a coboundary, and every short exact sequence `f : Hom N X`, `g : Hom X M` with `f.toLin`, `g.toLin` weight-preserving splits (`∃ s : Hom M X, Hom.comp g s = Hom.id M` and `∃ r : Hom X N, Hom.comp r f = Hom.id N`).
*Proof.* Induction on the `∇`-filtration of `N` by (V3), with the case `nabla A m` done by induction on the `Δ`-filtration of `M` by (V2) from (V1); the base cases have an empty basis on one side, where every cocycle is `0 = d0`. Then (G7).

**(V5)** If `A` is a domain of characteristic zero, the splitting in (V4) holds without the weight-preservation hypotheses on `f`, `g` (C25 (P1)). **(V6)** The case `A = ℤ_[2]`.

## Proof sketch (the delicate points)

(G2): write the glued `F^{(r)}`, `E^{(s)}` as 2 × 2 block matrices `[[N.F, cF], [0, M.F]]`; the upper-right block of a product of two block upper-triangular matrices is `N.X ∘ cY + cX ∘ M.Y`, linear in `c`; (K) at `δ_{inr i}` reads off the upper component, with the binomial coefficient evaluated at the weight `M.wt i` of `δ_{inr i}`. (G4): `[[1, ψ], [0, 1]]` conjugates the glued data of `0` into those of `dψ` (or check (G2) directly; (W) uses that `ψ` is weight-preserving, and the binomial coefficients in (K) agree because `ψ` preserves weights). (G6)(b): precompose the equations of (G2) with the surjection `p`, which commutes with the operators and preserves weights. (G7): `θ` is an `A`-linear bijection with inverse as given (`ρ ∘ f = id`, `g ∘ σ = id`, `ρ ∘ σ = 0`, `f ∘ ρ + σ ∘ g = id`); under `θ` the operators of `X` become the glued ones (upper-right block `ρ ∘ X.Fd r ∘ σ`, lower-left block `g ∘ X.Fd r ∘ f = 0`); so the glued data satisfy `IsDP` because those of `X` do (transport through `θ`). Weight-preserving linear sections and lifts exist: on each weight space separately (`pr w` commutes with weight-preserving maps, C25 (P2)).

## What is asked

Formalize and prove every statement above in a new folder `RequestProject/Cocycle/`, namespace `Cocycle`. Reuse the objects listed above; do not redefine them. Every isomorphism with its underlying maps stated. Every docstring names its part of this file. No `sorry`, no new axiom, no `native_decide`. Do not change the folders of C1–C26.
