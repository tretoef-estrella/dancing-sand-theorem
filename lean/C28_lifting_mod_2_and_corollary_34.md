# C28 — Lifting modulo 2 and Corollary 3.4

Piece C28 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §3: end of the proof of Lemma 3.3, and Corollary 3.4). Folder `RequestProject/Lift2/`, namespace `Lift2`.

## Setting (reused, not redefined)

- C18 (`DPLattice`): `DPLattice`, `IsDP`, `Hom`, `H`, `Hop`, `delta`, `nabla`.
- C19 (`WeylFilt`): `Hom.id`, `Hom.comp`, `Hom.ext'`, `ShortExact`.
- C20 (`Doubling`): `Iso`, `Hom.ofInverse`, `Iso.ofInverse`.
- C21 (`Twist`): `bc φ f` (base change of a linear map: the matrix of `f` with `φ` applied entrywise), `bc_comp`, `bc_id`, `bc_add`, `bc_smul`, `bc_single_apply`, `baseChange φ M` (basis `M.ι`, weights `M.wt`, operators `bc φ (M.Fd r)`, `bc φ (M.Ed r)`), `bcHom φ f`.
- C25 (`LemmaW`): `IsWtPres` («weight-preserving»: `ψ (δ_i) j = 0` whenever `M.wt i ≠ N.wt j`).
- C27 (`Cocycle`): `Lin`, `Pair`, `IsCocycle`, `CocycleEqs`, `G2`, `cocycles`, `d`, `G4`, `IsCoboundary`, `HasDeltaFilt`, `HasNablaFilt`, `V4`.

A vector of `M` is `M.ι → A`, `δ_i = Pi.single i 1`.

**Hypotheses on the rings.** `A`, `B` commutative rings, `φ : A →+* B` with
- (H1) `φ` surjective;
- (H2) `∀ a, φ a = 0 ↔ ∃ b, a = 2 * b` (the kernel of `φ` is `2A`);
- (H3) `∀ a, 2 * a = 0 → a = 0` (no 2-torsion).

The case of the paper is `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod` (Part Z).

## Part D — dividing by 2

**(D1)** Under (H2), (H3): if `T : Lin M N` and `bc φ T = 0`, there is a unique `U : Lin M N` with `T = 2 • U`; if `T` is weight-preserving, so is `U`.

**(D2)** Under (H3): if `2 • c` is a cocycle (C27), then `c` is a cocycle. (Every equation of (G2) is `L(c) = 0` with `L` additive, and `L(2 • c) = 2 • L(c)`.)

**(D3)** Under (H2), (H3): if `φ0 : Lin M N` is weight-preserving and `bc φ φ0` commutes with every `(baseChange φ M).Fd r`, `(baseChange φ M).Ed r` (that is, `bc φ (d φ0) = 0` in both components), then there is a pair `δ` with `d φ0 = 2 • δ`, and `δ` is a cocycle.

## Part L — lifting a morphism

**(L0)** Under (H1): for every weight-preserving `h̄ : (M.ι → B) →ₗ[B] (N.ι → B)` there is a weight-preserving `φ0 : Lin M N` with `bc φ φ0 = h̄`. (Lift each entry `h̄ (δ_i) j` by (H1), and put `0` where `M.wt i ≠ N.wt j`.)

**(L1)** A weight-preserving `h : Lin M N` with `d h = 0` is a morphism: there is `hh : Hom M N` with `hh.toLin = h`. (`d h = 0` is `h ∘ M.Fd r = N.Fd r ∘ h` and the same for `E`; `H` commutes with weight-preserving maps.)

**(L2) Lifting (end of the proof of Lemma 3.3).** Under (H1), (H2), (H3): if `HasDeltaFilt M` and `HasNablaFilt N`, then for every `h̄ : Hom (baseChange φ M) (baseChange φ N)` with `h̄.toLin` weight-preserving there is `h : Hom M N` with `h.toLin` weight-preserving and `bc φ h.toLin = h̄.toLin` (equivalently `bcHom φ h = h̄`).

*Proof.* (L0) gives `φ0`; (D3) gives `δ` with `d φ0 = 2 • δ`, a cocycle; C27 (V4) gives a weight-preserving `ψ` with `d ψ = δ`. Put `h := φ0 − 2 • ψ`: it is weight-preserving, `d h = d φ0 − 2 • d ψ = 0`, so it is a morphism (L1), and `bc φ h = bc φ φ0 − φ 2 • bc φ ψ = h̄` because `φ 2 = 0` (H2).

## Part C — Corollary 3.4

**(C1)** If every `1 + 2a` (`a : A`) is a unit of `A`, then for every finite type `ι` and every `u : Module.End A (ι → A)` of the form `u = 1 + 2 • w`, `u` is a unit (equivalently, bijective). (Its determinant is `≡ 1 modulo 2A`: `det (1 + 2 • W) = 1 + 2 · c` for an element `c`; or any other route.)

**(C2)** Under (H2), (H3) and the hypothesis of (C1): if `u : Module.End A (ι → A)` and `bc φ u = 1`, then `u` is bijective.

**(C3) Corollary 3.4.** Under (H1), (H2), (H3) and the hypothesis of (C1): let `X`, `Y` be DP-lattices over `A` with `HasDeltaFilt X`, `HasNablaFilt X`, `HasDeltaFilt Y`, `HasNablaFilt Y`, and let `ē : Iso (baseChange φ X) (baseChange φ Y)` with `ē.hom.toLin` and `ē.inv.toLin` weight-preserving. Then there is `e : Iso X Y` with `e.hom.toLin` and `e.inv.toLin` weight-preserving and `bc φ e.hom.toLin = ē.hom.toLin`, `bc φ e.inv.toLin = ē.inv.toLin`.

*Proof.* (L2) lifts `ē.hom` to `f : Hom X Y` and `ē.inv` to `g : Hom Y X`. Then `bc φ (g ∘ f) = 1`, so `g ∘ f` is bijective (C2), likewise `f ∘ g`; so `f` is bijective, and its inverse linear map is a morphism (`Hom.ofInverse`). The inverse of `f` reduces to `ē.inv` (it is `(g ∘ f)⁻¹ ∘ g` and `bc` is multiplicative). It is weight-preserving (the inverse of a bijective weight-preserving map is weight-preserving).

## Part Z — the case of the paper

**(Z1)** `φ = PadicInt.toZMod : ℤ_[2] →+* ZMod 2` satisfies (H1), (H2), (H3), and every `1 + 2a` with `a : ℤ_[2]` is a unit.

**(Z2)** (L2) and (C3) for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod`.

## Notes

- The weight-preservation of `h̄` and of `ē` is assumed. It is probably automatic (by Kostant's theorem the divided powers `E^{(r)}`, `F^{(r)}` generate every `binom(H, k)`, and over `ZMod 2` the values `binom(w, k) mod 2` for all `k` determine the integer `w`), but this is not used and not asked here. A `Hom` in the sense of C18 commutes with `F^{(r)}`, `E^{(r)}` and `H`, and `H` alone sees only weights modulo 2.
- Brute force (`chkC28.py`): over `ℤ` localized at 2, for `Δ`-filtered `M` and `∇`-filtered `N` among `Δ(l)`, `V ⊗ Δ(m)`, `V ⊗ V`, `V ⊗ V ⊗ V`, `∇(m)`, `V ⊗ ∇(m)`: every weight-preserving morphism modulo 2 is lifted by the procedure of (L2) (entries of `d φ0` even; `d ψ = δ` solvable with 2-integral `ψ`; `φ0 − 2ψ` commutes with every operator and reduces to `h̄`), and the reduction map on weight-preserving morphisms is onto. Controls: `Hom(Δ(0), Δ(2))` is `0` over ℚ and `1`-dimensional modulo 2 (so lifting fails without filtrations); `1 + 2W` is invertible over `ℤ_(2)` for random integer `W`, while a matrix `≡ 1` modulo 3 only can fail. A search for a non-weight-preserving morphism modulo 2 among the test lattices found none (consistent with the remark above).

## Sketch, in one place

`d` is additive. The pair `d φ0` has entries in `2A` because `bc φ (d φ0) = d̄ h̄ = 0` (base change is multiplicative and `h̄` is a morphism). `δ := d φ0 / 2` is a cocycle because `d φ0` is one (C27 (G4)) and the cocycle equations are additive, with no 2-torsion. Then C27 (V4).
