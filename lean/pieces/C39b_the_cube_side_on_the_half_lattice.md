# C39b — the cube side on the half-size lattice: Lemma 10.4(b) and Lemma 10.5(b)

Piece C39b of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §10.2, the cube side:
parts (b) of Lemmas 10.4 and 10.5). Folder `RequestProject/FoldCube/`, namespace `FoldCube`. The
folders C1–C39 are certified: do not change them.

## Setting (reuse, do not redefine)

- C18 `DPLattice` (`M.ι`, `M.wt`, `M.Fd`, `H M`), `DPLattice.bvec`, `DPLattice.tensorV` and its coproduct formulas `tensorV_Fd_b0`, `tensorV_Fd_b1`.
- C20 `Doubling.OddUnits`, `Doubling.phi` (basis `Fin 2 × N.ι`, weights `2·wt + wtV e`) and its formulas `Doubling.B1`, `Doubling.B3`.
- C38 `Fold.tauOp` (`tauOp M c = M.Fd 1 + (c : A) • 1 − H M`).
- C38b `FoldGroup.twoM` (and `twoMCongr`).
- C39 `FoldHalf.Psi`, `FoldHalf.glueOp`, `FoldHalf.beta`, `FoldHalf.betaInv`, `FoldHalf.betaEquiv`, `FoldHalf.PE`, `FoldHalf.QE`, `FoldHalf.E3`, `FoldHalf.E4`, `FoldHalf.E5`, `FoldHalf.A3`.
- C21/C29 `Filt.T` (`T_odd`, `T_even`); C32 `Families.sigL`, `Families.ds`, `Families.B2Z` / `sigEquivZ`; C16 `FamilyGroup.X`.

Throughout: `A` is a commutative ring; where `Doubling.phi` occurs, `[IsDomain A] [CharZero A] [Doubling.OddUnits A]`.

## Definitions (new), operators on a DP-lattice `M` (a vector of `M` is `M.ι → A`)

- `Jop M c := (c : A) • 1 − H M` for `c : ℤ` (so `tauOp M c = M.Fd 1 + Jop M c`).
- `Gp N d := N.Fd 1 − (2 : A) • (Jop N d * (Jop N d + 1))` (the paper's `G' = F + π'(D)`, `π'(f) = −2(j + 2f)(j + 2f + 1)`, with `d − H = j + 2D` on `T(l)`, `d = l + j`).
- `SigmaOp N e := N.Fd 1 + ((2 * e : ℤ) : A) • 1 − (2 : A) • H N` for `e : ℤ` (the paper's `Σ_c = F + 4(D + c)`; on `T(l)`, `4D = 2l − 2H`, so `Σ_c = SigmaOp (T l) (l + 2c)`).
- `halfJJ M c`: the diagonal operator multiplying the coordinate `i` by `((((c − M.wt i) * (c − M.wt i + 2)) / 2 : ℤ) : A)` (integer division).
- `thetaOp M c := M.Fd 2 + M.Fd 1 * (Jop M c + 2) + halfJJ M c` (the paper's `θ = τ(τ + 2)/2`).
- For `N`, `BN`, `d : ℤ`, `B : ℕ`, with `M := Doubling.phi N`:
  `thX N BN d B := LinearMap.fst ∘ₗ FoldHalf.betaInv N BN d ∘ₗ thetaOp M (2 * d + 1) ∘ₗ FoldHalf.beta N d B ∘ₗ LinearMap.inl`,
  `thY N BN d B := LinearMap.snd ∘ₗ FoldHalf.betaInv N BN d ∘ₗ thetaOp M (2 * d + 1) ∘ₗ FoldHalf.beta N d B ∘ₗ LinearMap.inl`
  (the blocks of `θ` in the basis `β` of C39 (E4)).

## Part O — the odd families (Lemma 10.4(b))

**(O1)** (elimination of the `b_1` slot) For every `N`, every `d : ℤ`:
  `((Doubling.phi N).ι → A) ⧸ range (Fold.tauOp (Doubling.phi N) (2 * d + 1)) ≃ₗ[A] (N.ι → A) ⧸ range ((2 : A) • Gp N d)`.
  *(Sketch: by B1, `τ(b_0 x_0 + b_1 x_1) = b_0[2 Jop N d x_0 + 2F x_1] + b_1[x_0 + 2(Jop N d + 1) x_1]`; the map `(y_0, y_1) ↦ y_0 − 2 Jop N d y_1` induces the isomorphism.)*

**(O2)** (halving) For an `A`-module `L` with `∀ x : L, (2 : ℕ) • x = 0 → x = 0` and every `G : Module.End A L`:
  `FoldGroup.twoM (L ⧸ range ((2 : A) • G)) ≃+ L ⧸ range G` (the class of `x` goes to `2·[x]`).
  Also: over `[IsDomain A] [CharZero A]`, `L = ι → A` satisfies the hypothesis.

**(O3)** (floor units) Let `N : DPLattice A` over `A` with `[Doubling.OddUnits A]`, and `W : ℤ` with **(top)** `∀ i, N.wt i ≤ W ∧ Even (W − N.wt i)`. For `d : ℤ` put `e := d` if `Even (d − W)` and `e := d + 1` otherwise. Then
  `(N.ι → A) ⧸ range (Gp N d) ≃ₗ[A] (N.ι → A) ⧸ range (SigmaOp N e)`.
  *(Sketch: let `u` be the diagonal operator with entries the odd one of `d − wt i`, `d − wt i + 1`, and `E` the even one, so `Gp N d = F − 2E·u`; `u` is a unit. Right multiplication by `−u^{−1}` gives `−F u^{−1} + 2E`, with `2E = SigmaOp N e − F`. With the floor `f_i := (W − wt i)/2` and the diagonal `s` with `s_i := Π_{g < f_i} (−u at weight W − 2g)`, conjugation by `s` turns `−F u^{−1}` into `F`, because `F` sends the coordinate of weight `w` to coordinates of weight `w − 2`. Neither step changes the cokernel.)*

**(O4)** (weights of the dance lattices) Over `[IsDomain A] [CharZero A] [Doubling.OddUnits A]`: `∀ i, (Filt.T A l).wt i ≤ l ∧ Even (l − (Filt.T A l).wt i)`.

**(O5)** (Lemma 10.4(b) over `ℤ_[2]`) For every `l, j : ℕ`, with `N := Filt.T ℤ_[2] l` and `c := (j + 1) / 2` (`= ⌈j/2⌉`):
  `FoldGroup.twoM (((Filt.T ℤ_[2] (2 * l + 1)).ι → ℤ_[2]) ⧸ range (Families.sigL ℤ_[2] (2 * l + 1) 1 j)) ≃+ (N.ι → ℤ_[2]) ⧸ range (SigmaOp N (l + 2 * c))`, and
  `FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j) ≃+ (N.ι → ℤ_[2]) ⧸ range (SigmaOp N (l + 2 * c))`.
  *(Uses `sigL ℤ_[2] (2l+1) 1 j = tauOp (T (2l+1)) (2(l + j) + 1)`, `T_odd`, (O1)–(O4) with `W = l`, `d = l + j`, `B2Z`.)*

## Part V — the even families (Lemma 10.5(b))

**(V1)** (modulo `τ`, `g ≡ 1 + τ_M`) For every DP-lattice `M` and every `c : ℤ`:
  `((DPLattice.tensorV M).ι → A) ⧸ range (Fold.tauOp (DPLattice.tensorV M) (c + 1)) ≃ₗ[A] (M.ι → A) ⧸ range (Fold.tauOp M c * (Fold.tauOp M c + 2))`.
  *(Sketch: `τ(b_0 m) = b_1 m + b_0 τ_M m`, `τ(b_1 m) = b_1 (τ_M + 2) m` with `τ_M = tauOp M c`; the map `(y_0, y_1) ↦ y_0 − τ_M y_1` induces the isomorphism.)*

**(V2)** (`θ = τ(τ + 2)/2`) If `∀ i, Even (c − M.wt i)`, then `(2 : A) • thetaOp M c = Fold.tauOp M c * (Fold.tauOp M c + 2)`. For `M = Doubling.phi N` and `c = 2 * d + 1` the hypothesis holds.

**(V3)** (`θ` in the basis `β`) For `N`, `BN` with (nil) `∀ s ≥ BN, N.Fd s = 0`, `d : ℤ`, `B ≥ 2 * BN`, `M = Doubling.phi N`, `c = 2 * d + 1`, `X := thX N BN d B`, `Y := thY N BN d B`, `P := FoldHalf.PE N BN d`, `Q := FoldHalf.QE N BN d`:
  (a) `thetaOp M c (FoldHalf.beta N d B (x, y)) = FoldHalf.beta N d B (X x + Y y, Y x + X y)`;
  (b) `(2 : A) • X = P * P + Q * Q + (2 : A) • P` and `(2 : A) • Y = P * Q + Q * P + (2 : A) • Q`;
  (c) `P − Q = FoldHalf.Psi N (d + 1) BN − 2`, `(2 : A) • (X + Y) = FoldHalf.Psi N d BN * (FoldHalf.Psi N d BN + 2)` and `(2 : A) • (X − Y) = (FoldHalf.Psi N (d + 1) BN − 2) * FoldHalf.Psi N (d + 1) BN`.

**(V4)** (circulant cokernels) For `A`-modules `L`, `M'`, an equivalence `β : (L × L) ≃ₗ[A] M'`, `w : Module.End A M'` and `X, Y : Module.End A L` with `w (β (x, y)) = β (X x + Y y, Y x + X y)` for all `x, y`:
  `M' ⧸ range w ≃ₗ[A] (L × L) ⧸ range (FoldHalf.glueOp (X − Y) (X + Y) Y)`.
  *(Sketch: the slot change `(u, v) ↦ (v − u, u)`; the image of `(x, y)` becomes `glueOp (X − Y) (X + Y) Y (y − x, x)`.)*

**(V5)** (Lemma 10.5(b), general form) Over `[IsDomain A] [CharZero A] [Doubling.OddUnits A]`, for `N`, `BN` with (nil), `d : ℤ`, `B ≥ 2 * BN`:
  `FoldGroup.twoM (((DPLattice.tensorV (Doubling.phi N)).ι → A) ⧸ range (Fold.tauOp (DPLattice.tensorV (Doubling.phi N)) (2 * d + 2))) ≃+ ((N.ι → A) × (N.ι → A)) ⧸ range (FoldHalf.glueOp (thX N BN d B − thY N BN d B) (thX N BN d B + thY N BN d B) (thY N BN d B))`.

**(V6)** (Lemma 10.5(b) over `ℤ_[2]`) For every `l, i : ℕ`, with `N := Filt.T ℤ_[2] l`, `d := l + i`, `BN := l + 1`, `B := 2 * l + 2`:
  `FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i) ≃+ ((N.ι → ℤ_[2]) × (N.ι → ℤ_[2])) ⧸ range (FoldHalf.glueOp (thX N BN d B − thY N BN d B) (thX N BN d B + thY N BN d B) (thY N BN d B))`.
  *(Uses `sigL ℤ_[2] (2l+2) 1 i = tauOp (T (2l+2)) (2(l + i) + 2)`, `T_even`, C39 (A3) for (nil), (V5), `B2Z`.)*

## Checks done before sending

- Brute force (`chkC39b.py`, independent lattice model of `T(λ)` from `chkC38b.py`, exact rationals, 2-adic Smith forms): weights of `T(l)` (`l ≤ 8`); (O1) `l ≤ 6`, every `d ∈ [−2, l + 5]`; (O3) the same range; (O5) `l ≤ 6`, `j ≤ 5`; (V1) every `M = T(m)`, `m ≤ 8`, every `c ∈ [−3, m + 4]`; (V2) on `Φ(T(l))`, `l ≤ 6`, with `θ` integral; (V3) `θ β = β·circ(X, Y)`, `X`, `Y` integral, the identities of (b), (c), `l ≤ 5`; (V6) `l ≤ 5`, `i ≤ 4`. `logs/chkC39b.log`.
- Controls (all four must fire): `Σ` at `e = d` for odd `j`; the glue without its lower-left block; the even family at the wrong `d` (`l + i + 1`); (O1) without the factor `2`.

## Instructions

Encodings are your choice provided they are faithful; say in a docstring how each object is encoded. Keep the statements exactly as in this file (more general statements are fine if noted; say if a hypothesis is unused). Every docstring should name the part of `C39b_the_cube_side_on_the_half_lattice.md` it corresponds to. No `sorry`, no new axiom, no `native_decide`.
- Two candidate controls could not fire and were replaced (declared): exchanging the two arms of the glue, and replacing the arm `Ψ_d(Ψ_d + 2)/2` by `Ψ_d(Ψ_d − 2)/2` or by `Ψ_d` alone — the 2-adic Smith form does not change in any cell tried (`l ≤ 3`, `i ≤ 2`). Measured only; nothing is claimed about it.
