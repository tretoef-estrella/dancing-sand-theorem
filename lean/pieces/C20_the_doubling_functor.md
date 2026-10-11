# The doubling functor `Φ` (Proposition 3.1 (a), (b), (d))

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §3.1, Proposition 3.1 (a), (b), (d). This is the fourth piece of stage 1c. It reuses piece C18 (`RequestProject/DPLattice/`: `DPLattice`, `DPLattice.IsDP`, `DPLattice.H`, `DPLattice.Hom`, `DPLattice.one`, `DPLattice.V`, `DPLattice.delta`, `DPLattice.nabla`, `DPLattice.T5_delta_zero`, `DPLattice.T5_nabla_zero`, `DPLattice.T5_delta_one`, `DPLattice.T5_nabla_one`) and piece C19 (`RequestProject/WeylFilt/`: `WeylFilt.Hom.id`, `WeylFilt.Hom.comp`, `WeylFilt.ShortExact`). Part (c) (the reduction modulo 2) is a later piece.

The paper proves (d) by Weyl's theorem on complete reducibility over `ℚ`. Here the isomorphisms are given **explicitly** (a diagonal map with odd ratios), and it is checked directly that they commute with every `F^{(r)}`, `E^{(s)}` and `H`; no argument over `ℚ` and no complete reducibility is needed for (d).

## Setting

`A` is a commutative ring which is a domain of characteristic zero and in which **every odd integer is a unit**: `[IsDomain A] [CharZero A]` and `hodd : ∀ k : ℕ, IsUnit ((2 * k + 1 : ℕ) : A)`. (The ring of the paper, `ℤ_2`, is such a ring; state this as an instance check for `ℤ_[2]`.) For an odd natural number `k` write `k!!` for the double factorial (`(−1)!! = 1!! = 1`) and `⅟k!!` for its inverse in `A`.

`N` is a DP-lattice (C18). For `i : N.ι` write `w_i := N.wt i`, `e_i := Pi.single i 1`, `F := N.Fd 1`, `E := N.Ed 1`. For a list of integers `c_1, …, c_t` and a vector `x` of `N` write
  `Π_{c}(x) := (4FE + c_1)(4FE + c_2) ⋯ (4FE + c_t)(x)`
(the factors commute; the empty product is the identity).

**The lattice `Φ(N)`.** Basis `Fin 2 × N.ι`; the vector with `n` in slot `e` is `b_e n` (`bvec e n` of C18). Weights: `wt(0, i) = 2w_i + 1`, `wt(1, i) = 2w_i − 1`. For `s ≥ 0`, on basis vectors (and extended `A`-linearly):

- `F^{(2s)}(b_e e_i) = ⅟(2s−1)!! · b_e F^{(s)} e_i` (`e = 0, 1`);
- `F^{(2s+1)}(b_0 e_i) = ⅟(2s+1)!! · b_1 F^{(s)} e_i`;
- `F^{(2s+1)}(b_1 e_i) = (2s+2)·⅟(2s+1)!! · b_0 F^{(s+1)} e_i`;
- `E^{(2s)}(b_1 e_i) = ⅟(2s−1)!! · b_1 Π_{c}(E^{(s)} e_i)`, `c_j = (w_i+2s+1)² − (w_i+2j)²`, `0 ≤ j < s`;
- `E^{(2s+1)}(b_1 e_i) = ⅟(2s+1)!! · b_0 Π_{c}(E^{(s)} e_i)`, `c_j = (w_i+2s+1)² − (w_i+2j)²`, `0 ≤ j ≤ s`;
- `E^{(2s)}(b_0 e_i) = ⅟(2s−1)!! · b_0 Π_{c}(E^{(s)} e_i)`, `c_j = (w_i+2s+1)² − (w_i+2j)²`, `1 ≤ j ≤ s`;
- `E^{(2s+1)}(b_0 e_i) = 2(s+1)·⅟(2s+1)!! · b_1 Π_{c}(E^{(s+1)} e_i)`, `c_j = (w_i+2s+3)² − (w_i+2j)²`, `1 ≤ j ≤ s`.

For `r = 1` these are the formulas of the paper: `F(b_0 n) = b_1 n`, `F(b_1 n) = 2 b_0 F n`, `E(b_0 n) = 2 b_1 E n`, `E(b_1 n) = b_0 (4FE + 2w + 1) n` (`n` of weight `w`), `H(b_0 n) = (2w+1) b_0 n`, `H(b_1 n) = (2w−1) b_1 n`.

**`Φ` on morphisms.** For `f : Hom N M`, `Φ(f) := 1 ⊗ f`, i.e. `Φ(f)(b_e n) = b_e f(n)`.

## Part A — `Φ(N)` is a DP-lattice and `Φ` is an exact functor (Prop. 3.1 (a))

**(A1)** The data above satisfy `IsDP` (C18: (W) for `F` and `E`, (P0), (P1) for `F` and `E`, (K)); so `Φ(N)` is a DP-lattice, `phi N : DPLattice A`.
**(A2)** `Φ(f)` is a morphism `Hom (phi N) (phi M)`; `Φ(Hom.id N) = Hom.id (phi N)`; `Φ(g ∘ f) = Φ(g) ∘ Φ(f)`.
**(A3)** `Φ` is exact: if `X —f→ Y —g→ Z` is a short exact sequence (C19 `ShortExact`) then so is `Φ(X) —Φ(f)→ Φ(Y) —Φ(g)→ Φ(Z)`.

## Part B — the divided powers of `F` (Prop. 3.1 (b))

**(B1)** The single operators: `F^{(1)}`, `E^{(1)}`, `H` of `phi N` are given by the `r = 1` formulas above.
**(B2)** For every `r`, `(r!) • F^{(r)} = (F^{(1)})^r` and `(r!) • E^{(r)} = (E^{(1)})^r` on `phi N` (so the closed formulas are the divided powers of the single operators).
**(B3)** The formulas of (b) as stated in the paper: `F^{(2s)}(b_e n) = ⅟(2s−1)!! · b_e F^{(s)} n`, `F^{(2s+1)}(b_0 n) = ⅟(2s+1)!! · b_1 F^{(s)} n`, `F^{(2s+1)}(b_1 n) = (2s+2)·⅟(2s+1)!! · b_0 F^{(s+1)} n`, for every vector `n` (not only basis vectors).

## Part D — `Φ` on Weyl lattices (Prop. 3.1 (d))

Order the basis of `Φ(Δ_A(μ))` (and of `Φ(∇_A(μ))`) by weight: the `R`-th vector `x_R` is `b_0 e_s` if `R = 2s` and `b_1 e_s` if `R = 2s + 1` (`0 ≤ R ≤ 2μ + 1`).

**(D1)** The `A`-linear map `δ_μ : Δ_A(2μ+1) → Φ(Δ_A(μ))`, `e'_R ↦ c_R x_R` with `c_{2s} = ⅟(2s−1)!!`, `c_{2s+1} = ⅟(2s+1)!!`, is a morphism of DP-lattices and is bijective, with inverse `x_R ↦ c_R^{-1} e'_R`. So `Φ(Δ_A(μ)) ≅ Δ_A(2μ+1)` (morphisms both ways, composites the identities).
**(D2)** The `A`-linear map `ν_μ : ∇_A(2μ+1) → Φ(∇_A(μ))`, `w'_R ↦ d_R x_R` with `d_0 = 1`, `d_{2s+1} = d_{2s} · ⅟(2μ+1−2s)`, `d_{2s+2} = d_{2s+1}`, is a morphism of DP-lattices and is bijective. So `Φ(∇_A(μ)) ≅ ∇_A(2μ+1)`.
**(D3)** `Φ(one A) ≅ V A` (morphisms both ways, composites the identities): from (D1) with `μ = 0` and C18 (T5) `Δ_A(0) ≅ 𝟙`, `Δ_A(1) = V`.

*Proof sketch.* (A1): (W), (P0) by inspection. For (P1) and (K) use that `A` is a domain of characteristic zero: by (P1) on `N`, `t! F^{(t)} = F^t` and `t! E^{(t)} = E^t` on `N`, and (B2) on `Φ(N)` (by induction on `r` from the closed formulas, using (K) on `N` to commute `E` past `F^{(a)}`, the identity `E·f(H) = f(H − 2)·E`, and that `Ω := 4FE + (H+1)²` commutes with `E`, `F`, `H` on `N`); then (P1) for `Φ(N)` is `C(a+b, a)·a!b! = (a+b)!` after multiplying by `a! b!`, and (K) for `Φ(N)` after multiplying by `r! s!` reduces to the Lie relations `[E, F] = H`, `[H, E] = 2E`, `[H, F] = −2F` of the single operators, which hold on `Φ(N)` (on `b_0 n`: `EF − FE = 4FE + 2w + 1 − 4FE = 2w + 1`; on `b_1 n`: `4EF − 4FE − 2w − 1 = 2w − 1`) — in characteristic zero the divided-power relations follow from the Lie relations. Cancel the nonzero integers since `A` is a domain of characteristic zero. (A2), (A3): `Φ(f) = 1 ⊗ f` and every formula uses only the action on `N`; as `A`-modules `Φ(N) = N²`. (D1), (D2): the ratios are odd, so the maps are invertible; commutation with `F^{(1)}` is the computation `c_{2s} = (2s+1)c_{2s+1}`, `c_{2s+2} = c_{2s+1}` (resp. `d_{2s} = (2μ+1−2s)d_{2s+1}`, `d_{2s+1} = d_{2s+2}`), with `H` by weights, with `E^{(1)}` directly on basis vectors (`E` on `Δ(2μ+1)` is `E e'_R = (2μ+2−R) e'_{R−1}`, on `Φ(Δ(μ))` by the formulas above, and `FE e_s = s(μ−s+1) e_s` on `Δ(μ)`); then with every divided power by (B2) and the domain/characteristic-zero cancellation.
