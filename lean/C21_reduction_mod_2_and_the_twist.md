# Reduction modulo 2 and the Frobenius twist (Proposition 3.1 (c))

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §3.1, Proposition 3.1 (c), and the notion «`M^{[1]}` is the Frobenius twist» used there and in Lemma 3.5. This is the fifth piece of stage 1c.

It reuses:
- piece C18 (`RequestProject/DPLattice/`): `DPLattice`, `DPLattice.IsDP`, `DPLattice.H`, `DPLattice.Hom`, `DPLattice.V`, `DPLattice.tensorV`, `DPLattice.bvec`, `DPLattice.slice`, `DPLattice.InWt`;
- piece C19 (`RequestProject/WeylFilt/`): `WeylFilt.Hom.id`, `WeylFilt.Hom.comp`;
- piece C20 (`RequestProject/Doubling/`): `Doubling.OddUnits`, `Doubling.dfi`, `Doubling.piOp`, `Doubling.phi`, `Doubling.Iso`.

Lemma 3.5 (`V^{⊗3}` over `𝔽_2`) is the next piece.

## Setting

- `A` is a commutative ring with `[IsDomain A] [CharZero A] [Doubling.OddUnits A]` (the setting of C20).
- `B` is a commutative ring in which `2 = 0`: hypothesis `h2 : (2 : B) = 0`. The case of the paper is `B = 𝔽_2 = ZMod 2`.
- `φ : A →+* B` is a ring homomorphism. The case of the paper is `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod`; state the instance check that it satisfies the hypotheses, `PadicInt.toZMod (2 : ℤ_[2]) = 0` included.

For a type `ι` with `Fintype` and `DecidableEq`, a `B`-vector is `ι → B`; the basis vector is `δ_i = Pi.single i 1`.

## Part R — base change of a DP-lattice along a ring homomorphism

Here `A`, `B` are any commutative rings and `φ : A →+* B` any ring homomorphism.

For an `A`-linear endomorphism `f` of `ι → A`, write `f^φ` for the `B`-linear endomorphism of `ι → B` whose matrix is the matrix of `f` with `φ` applied to every entry:
  `f^φ (δ_i) j = φ (f (δ_i) j)`.
(Equivalently, `f^φ = Matrix.toLin' ((LinearMap.toMatrix' f).map φ)`.)

For a DP-lattice `M` over `A`, `M^φ` has:
- the same basis `M.ι` and the same weights `M.wt`;
- `F^{(r)} := (M.Fd r)^φ` and `E^{(r)} := (M.Ed r)^φ`.

For a morphism `f : Hom M N`, `f^φ` is defined likewise on its matrix.

**(R0)** For every `x : ι → A`, `f^φ (φ ∘ x) = φ ∘ (f x)`. Also:
- `(f ∘ g)^φ = f^φ ∘ g^φ`;
- `1^φ = 1`;
- `(c • f)^φ = φ(c) • f^φ`.

**(R1)** `M^φ` satisfies `IsDP`: (W), (P0), (P1) and (K). So `M^φ : DPLattice B` (`baseChange φ M`).

**(R2)** For `f : Hom M N`, `f^φ` is a `Hom (M^φ) (N^φ)`. Moreover:
- `(Hom.id M)^φ = Hom.id (M^φ)`;
- `(g ∘ f)^φ = g^φ ∘ f^φ`.

**(R3)** `(V A)^φ ≅ V B` and `(tensorV M)^φ ≅ tensorV (M^φ)`.

Here an isomorphism is a `Doubling.Iso`: `Hom`s both ways whose composites are `Hom.id`. In both cases the underlying linear maps are the identity of `Fin 2 → B`, respectively of `Fin 2 × M.ι → B`.

## Part T — the Frobenius twist (`2 = 0` in `B`)

**(T0) Lucas at 2.** For every integer `x` and every `j : ℕ`, in `B` (where `2 = 0`):
- `(Ring.choose (2x) (2j) : B) = (Ring.choose x j : B)`;
- `(Ring.choose (2x) (2j + 1) : B) = 0`.

Here `x` may be negative. For `x ≥ 0` this is Lucas' theorem at the prime 2 for the last binary digit.

**The twist.** For a DP-lattice `M` over `B`, `M^{[1]}` (`frob M`) has:
- the basis `M.ι`;
- the weights `wt^{[1]}(i) = 2·M.wt i`;
- `F^{(r)} := M.Fd (r/2)` if `r` is even and `0` if `r` is odd;
- `E^{(r)} := M.Ed (r/2)` if `r` is even and `0` if `r` is odd.

That is: `F^{(2s)}`, `E^{(2s)}` act as `F^{(s)}`, `E^{(s)}`; the odd divided powers act as `0`; and `H` acts as `2H`.

**(T1)** If `2 = 0` in `B`, then `M^{[1]}` satisfies `IsDP`. So `M^{[1]} : DPLattice B`.
- For (P1), use (T0).
- For (K) at `(i, r, s)`:
  - if `r` or `s` is odd, both sides are `0`;
  - if `r` and `s` are both odd, use the second identity of (T0);
  - if `r = 2r'` and `s = 2s'`, the only surviving terms are `j = 2j'`; there, with `x = M.wt i + s' − r'`, the first identity of (T0) reduces (K) for `M^{[1]}` at `(i, 2r', 2s')` to (K) for `M` at `(i, r', s')`.

**(T2)** For `f : Hom M N`, the same linear map is a `Hom (M^{[1]}) (N^{[1]})`. This sends `Hom.id` to `Hom.id` and composites to composites.

## Part C — Proposition 3.1 (c): `Φ(N) ⊗ 𝔽_2 ≅ V ⊗ (N ⊗ 𝔽_2)^{[1]}`

Let `N` be a DP-lattice over `A`, and `N̄ := N^φ`.

**(C0) The constants become 1.**
- `φ(dfi s) = 1` for every `s`, i.e. `⅟(2s−1)!!` reduces to `1`.
- `φ(2s + 2) = 0`.
- `φ(2(s + 1)) = 0`.
- For every integer `w` and every `0 ≤ j ≤ s`, the integer `c_j = (w + 2s + 1)² − (w + 2j)²` is odd, so `φ(c_j) = 1`.
- For every `s`, `0 ≤ j ≤ s − 1`, the integer `(w + 2s + 3)² − (w + 2(j + 1))²` is odd.
- Consequently `(Doubling.piOp N S c)^φ = 1` whenever every `c j`, `j ∈ S`, is odd.

**(C1) The formulas modulo 2.** On `(Φ(N))^φ`, for every `s ≥ 0`, every `e` and every vector `n : N.ι → B`:
- `F^{(2s)}(b_e n) = b_e F^{(s)} n`;
- `F^{(2s+1)}(b_0 n) = b_1 F^{(s)} n`;
- `F^{(2s+1)}(b_1 n) = 0`;
- `E^{(2s)}(b_e n) = b_e E^{(s)} n`;
- `E^{(2s+1)}(b_1 n) = b_0 E^{(s)} n`;
- `E^{(2s+1)}(b_0 n) = 0`.

Here `F^{(s)}`, `E^{(s)}` are those of `N̄`, and `b_e n = bvec e n`. Prove these first on basis vectors `n = δ_i`, then extend linearly.

**(C2) Proposition 3.1 (c).** `(Φ(N))^φ ≅ tensorV ((N̄)^{[1]})`, by the isomorphism whose underlying linear maps (both ways) are the identity of `Fin 2 × N.ι → B`.

The two bases are both `Fin 2 × N.ι`, and the weights agree: `2w_i + wtV e = wtV e + 2w_i`. On `V ⊗ M` (C18), with the coproduct:
- `F^{(r)}(b_0 m) = b_0 F^{(r)} m + b_1 F^{(r−1)} m`;
- `F^{(r)}(b_1 m) = b_1 F^{(r)} m`;
- `E^{(r)}(b_1 m) = b_1 E^{(r)} m + b_0 E^{(r−1)} m`;
- `E^{(r)}(b_0 m) = b_0 E^{(r)} m`.

For `M = N̄^{[1]}`, these are exactly the formulas of (C1).

**(C3) The case of the paper.** For `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod` and every DP-lattice `N` over `ℤ_[2]`:
  `Nonempty (Doubling.Iso ((Doubling.phi N)^φ) (tensorV ((N^φ)^{[1]})))`.

*Proof sketch.*
- **(R1).** Every axiom of `M` is an identity among the matrices of `M.Fd`, `M.Ed` with integer scalars. Applying the ring homomorphism `φ` entrywise (`Matrix.map` is multiplicative) gives the same identity for `M^φ`, because `φ` sends the integer `k` to `(k : B)`.
- **(R3).** For `V` the matrices have entries `0, 1`. For `tensorV` the coproduct formulas are entrywise sums of the entries of `M`.
- **(T0).** Over `ℤ[X]` reduced modulo `2`, `(1 + X)^2 = 1 + X^2`, hence `(1 + X)^{2a} = (1 + X^2)^a` for `a ≥ 0`. For negative tops, use `Ring.choose (−a) k = (−1)^k C(a + k − 1, k)` and the case `a ≥ 0`, or induction on `x` in both directions with Pascal's rule `C(x + 1, k + 1) = C(x, k) + C(x, k + 1)`.
- **(C0).** `(2s − 1)!!` is odd. A unit `u` with `φ(u) = 1 + 2t` maps to `1` because `2 = 0`, and so does its inverse. `c_j = (2s − 2j + 1)(2w + 2s + 2j + 1)`.
- **(C1).** Apply φ to the closed formulas of C20 (`phiFd_even`, …, `phiEd_odd_b0`) and use (C0). In `4FE + c_j`, `φ(4) = 0` and `φ(c_j) = 1`.
- **(C2).** By (C1) and the coproduct formulas of C18 (`tensorV_Fd_b0`, …), the identity commutes with every `F^{(r)}` and `E^{(r)}` and with `H`.
