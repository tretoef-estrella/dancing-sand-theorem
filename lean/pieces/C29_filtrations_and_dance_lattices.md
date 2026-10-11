# C29 — Filtrations of V ⊗ −, Φ, ⊕ and of the dance lattices T(λ)

Piece C29 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §3.3, the sentence «By Lemma 2.4 and Proposition 3.1(d), every `T(λ)` and every `V^{⊗n} ⊗ A` has a `Δ`-filtration and a `∇`-filtration (both operations preserve each kind of filtration)», and the definition of the dance lattices). Folder `RequestProject/Filt/`, namespace `Filt`. The assembly of Theorem 3.6 is the next piece, C30; it needs exactly the filtrations proved here.

## Setting (reused, not redefined)

- C18 (`DPLattice`): `DPLattice`, `IsDP`, `Hom`, `H`, `delta`, `nabla`, `one`, `V`, `tensorV`, `T5_delta_zero`, `T5_nabla_zero`, `T5_delta_one`, `T5_nabla_one`.
- C19 (`WeylFilt`): `Hom.id`, `Hom.comp`, `Hom.ext'`, `ShortExact`, `fDelta`, `gDelta`, `fNabla`, `gNabla`, `S1`, `S2`, `S4`, `Hom.ofEq`.
- C20 (`Doubling`): `phi`, `phiHom`, `A2`, `A3`, `Iso`, `Iso.ofInverse`, `Iso.trans`, `Iso.symm`, `Iso.ofDataEquiv`, `deltaIso`, `nablaIso`, `OddUnits`.
- C22 (`Lemma35`): `dsum`, `inlHom`, `inrHom`, `fstHom`, `sndHom`, `dsumHom`.
- C23 (`Tensor2`): `tensorVHom`, `tensorVHom_bvec`, `tensorVHom_id`, `tensorVHom_comp`.
- C25 (`LemmaW`): `IsWtPres`, `P1` (over a domain of characteristic zero every morphism is weight-preserving).
- C27 (`Cocycle`): `HasDeltaFilt`, `HasNablaFilt`, `G7`, `zeroL`.
- C28 (`Lift2`): `isWtPres_inverse`.

`HasDeltaFilt M` (C27): `M.ι` empty, or there are weight-preserving `f : Hom M' M`, `g : Hom M (delta A l)` short exact with `HasDeltaFilt M'` (a `Δ` on top). `HasNablaFilt N`: `N.ι` empty, or weight-preserving `f : Hom (nabla A m) N`, `g : Hom N N'` short exact with `HasNablaFilt N'` (a `∇` at the bottom).

`A` is a commutative ring. Statements marked **[char 0]** assume `[IsDomain A] [CharZero A]`; statements marked **[Φ]** assume `[IsDomain A] [CharZero A] [OddUnits A]` (the setting in which C20's `phi` is a DP-lattice). More general statements are welcome if noted.

## Part S — sub-lattices and quotient lattices

**(S1) Sub-lattice.** Let `X` be a DP-lattice, `κ` a finite type with decidable equality and weights `wK : κ → ℤ`, and `j : (κ → A) →ₗ[A] (X.ι → A)`, `p : (X.ι → A) →ₗ[A] (κ → A)` with `p ∘ j = id`, `j` weight-preserving (`j (δ_k) i = 0` when `wK k ≠ X.wt i`), `p` weight-preserving, and `range j` stable under every `X.Fd r`, `X.Ed r`. Then there is a DP-lattice `sub X j p …` with basis `κ`, weights `wK`, operators `Fd r = p ∘ X.Fd r ∘ j`, `Ed r = p ∘ X.Ed r ∘ j`, and `j` is a morphism `sub … → X`.

**(S2) Quotient lattice.** Let `X` be a DP-lattice, `κ`, `wK` as above, `q : (X.ι → A) →ₗ[A] (κ → A)`, `s : (κ → A) →ₗ[A] (X.ι → A)` with `q ∘ s = id`, both weight-preserving, and `ker q` stable under every `X.Fd r`, `X.Ed r`. Then there is a DP-lattice `quot X q s …` with basis `κ`, weights `wK`, operators `Fd r = q ∘ X.Fd r ∘ s`, `Ed r = q ∘ X.Ed r ∘ s`, and `q` is a morphism `X → quot …`.

(Proof idea: every identity of `IsDP` for the new operators is the corresponding identity for `X` transported by `j`, `p` (resp. `q`, `s`): `j ∘ (p ∘ T ∘ j) = T ∘ j` for each operator `T` because `range j` is stable and `j ∘ p` is the identity on `range j`; dually `(q ∘ T ∘ s) ∘ q = q ∘ T` because `ker q` is stable and `s ∘ q − id` maps into `ker q`.)

## Part I — invariance under isomorphism

**(I1)** If `e : Iso X Y` with `e.hom.toLin` and `e.inv.toLin` weight-preserving, then `HasDeltaFilt X → HasDeltaFilt Y` and `HasNablaFilt X → HasNablaFilt Y`.

**(I2)** `HasDeltaFilt (one A)`, `HasNablaFilt (one A)`, `HasDeltaFilt (V A)`, `HasNablaFilt (V A)` (from `delta A 0`, `nabla A 0` by `T5_delta_zero`, `T5_nabla_zero`, and `T5_delta_one`, `T5_nabla_one`).

## Part E — extensions

**(E1)** If `f : Hom M' M`, `g : Hom M Q` are short exact and weight-preserving, `HasDeltaFilt M'` and `HasDeltaFilt Q`, then `HasDeltaFilt M`.

*Sketch.* Induction on `HasDeltaFilt Q`, for all `M'`, `M`, `f`, `g`. If `Q.ι` is empty, `f` is bijective; use (I1) (the inverse is weight-preserving, C28 `isWtPres_inverse`). Step `f' : Hom Q' Q`, `g' : Hom Q (delta A l)`: by C27 (G7) for `(f, g)` and for `(f', g')` take weight-preserving `σ, ρ` with `g σ = id`, `ρ f = id`, `f ρ = id − σ g`, and `σ', ρ'` likewise. Put `κ := M'.ι ⊕ Q'.ι`, `j (u, v) := f u + σ (f' v)`, `p x := (ρ (x − σ (f' (ρ' (g x)))), ρ' (g x))`. Then `p ∘ j = id`, `range j = g⁻¹(range f')` is stable, so (S1) gives `K`; `M' → K → Q'` (`u ↦ (u, 0)`, `(u, v) ↦ v`) is short exact and weight-preserving, so `HasDeltaFilt K` by the induction hypothesis; and `j : K → M`, `g' ∘ g : M → delta A l` are short exact (`ker (g' g) = g⁻¹(ker g') = g⁻¹(range f') = range j`). So `HasDeltaFilt M` by the step constructor.

**(E2)** If `f : Hom N' N`, `g : Hom N N''` are short exact and weight-preserving, `HasNablaFilt N'` and `HasNablaFilt N''`, then `HasNablaFilt N`. (Dually, by induction on `HasNablaFilt N'` with the quotient lattice (S2), or by the contravariant dual of C25 if that is shorter.)

**(E3)** `HasDeltaFilt M → HasDeltaFilt N → HasDeltaFilt (dsum M N)`, and the same for `HasNablaFilt` (by (E1), (E2) applied to `inlHom`, `sndHom`).

## Part V — the two operations

**(V1) [char 0]** `HasDeltaFilt M → HasDeltaFilt (tensorV M)` and `HasNablaFilt N → HasNablaFilt (tensorV N)`.

*Sketch.* Induction on the filtration. `tensorV` of an empty lattice is empty. `tensorVHom` sends short exact sequences to short exact sequences (it is `id ⊠ f` on `Fin 2 × ι → A`). `V ⊗ Δ(l)` has a `Δ`-filtration: for `l ≥ 1`, C19 (S1): `fDelta : Δ(l+1) → V ⊗ Δ(l)`, `gDelta : V ⊗ Δ(l) → Δ(l−1)` short exact; for `l = 0`, `V ⊗ Δ(0) ≅ V = Δ(1)` (C19 (S4), (I1), (I2)). Likewise `V ⊗ ∇(l)` (C19 (S2): `fNabla : ∇(l−1) → V ⊗ ∇(l)`, `gNabla : V ⊗ ∇(l) → ∇(l+1)`). Then (E1), (E2). Every morphism is weight-preserving here (C25 (P1)).

**(V2) [Φ]** `HasDeltaFilt M → HasDeltaFilt (phi M)` and `HasNablaFilt N → HasNablaFilt (phi N)`.

*Sketch.* Induction; `phi` of an empty lattice is empty; `phiHom` is exact (C20 (A3)); `phi (delta A l) ≅ delta A (2l+1)` and `phi (nabla A l) ≅ nabla A (2l+1)` (C20 `deltaIso`, `nablaIso`); then (I1), (E1), (E2).

## Part T — the dance lattices and the tensor powers

**(T0)** Define `T : ℕ → DPLattice A` [Φ] by
  `T 0 = one A`,  `T (2l+1) = phi (T l)`,  `T (2l+2) = tensorV (phi (T l))`
(well-founded recursion; state the three equations as theorems), and `tpow : ℕ → DPLattice A` by `tpow 0 = one A`, `tpow (n+1) = tensorV (tpow n)` (`V^{⊗n} ⊗ A`).

**(T1) [Φ]** For every `λ`: `HasDeltaFilt (T λ)` and `HasNablaFilt (T λ)`.

**(T2) [char 0]** For every `n`: `HasDeltaFilt (tpow n)` and `HasNablaFilt (tpow n)`.

**(T3) [Φ]** For every DP-lattice `N` with `HasDeltaFilt N` and `HasNablaFilt N`, the two lattices of C24 (Lemma 3.5, second sentence),
  `tensorV (tensorV (phi N))`  and  `dsum (dsum (phi N) (phi N)) (phi (tensorV N))`,
both have a `Δ`-filtration and a `∇`-filtration. In particular this holds for `N = T l`, every `l`.

## Part Z — the case of the paper

**(Z1)** (T1), (T2), (T3) for `A = ℤ_[2]` (Mathlib's `PadicInt 2`, with C20's instance `OddUnits ℤ_[2]`).

## Notes

- Nothing is cited: (S1), (S2) are linear algebra; (E1) is the induction above; (V1), (V2) use only C19, C20, C23.
- Brute force (`chkC29.py`), over `ℤ` localized at `2` and over `𝔽_2`: `T(λ)` (`λ ≤ 7`), `V^{⊗n}` (`n ≤ 4`) and the two lattices of (T3) for `N = T(l)`, `l ≤ 2`, are DP-lattices; ranks and characters are those of §3.3; for each of them and every `m`, `dim_ℚ Hom(X, ∇(m)) = dim_{𝔽_2} Hom(X/2, ∇(m)/2)` and `dim_ℚ Hom(Δ(m), X) = dim_{𝔽_2} Hom(Δ(m)/2, X/2)` (a necessary consequence of the two filtrations by C27–C28), and these dimensions are the `Δ`- and `∇`-multiplicities predicted by the rules `V ⊗ Δ(l) ↝ Δ(l+1) + Δ(l−1)`, `Φ(Δ(l)) ↝ Δ(2l+1)`. Controls: `∇(2)` fails the `Δ`-test (`Hom(∇(2), ∇(0))` is `0` over `ℚ` and `1`-dimensional modulo `2`); a wrong `Φ` fails.
