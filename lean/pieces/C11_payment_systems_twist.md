# Payment systems and the twist move (Proposition 4.1, §4.1–§4.2)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §4.1 (payment systems) and Proposition 4.1 (the twist move). The statement is proved here over **any commutative ring `A`** and in a **scaled form**, `coker(c·G)` for every `c ∈ A`; the paper's Proposition 4.1 is the case `c = 1`, and the case `c = 2^h` is what the proof of Proposition 4.3 uses at each move. The split move (Proposition 4.2) comes in the next piece.

No earlier piece is needed (only Mathlib).

## Setting

`A` is a commutative ring.

**Graded families.** A *graded family* is an index type `ι` (with decidable equality), a *floor* function `fl : ι → ℕ`, a family of `A`-modules `N i` (`i ∈ ι`), and an `A`-linear map `F : ⨁_{i∈ι} N i → ⨁_{i∈ι} N i` (the operator `F`). Write `M := ⨁_{i∈ι} N i` (the direct sum; elements have finite support). An element of `N i` placed at index `i` has floor `fl i`. (In the paper `F` raises the floor by one; that is not needed for the statements below, so it is not assumed.)

**Slots.** A *slot type* is a finite type `S` with a linear order. The module of a system of size `|S|` is `M^S := ⨁_{(s, i) ∈ S × ι} N i`; for `x ∈ N i` write `x ι_{s,i}` for `x` placed at `(s, i)`, and for `m ∈ M` write `m ι_s` for `m` placed in slot `s` (the linear map `M → M^S` sending `x` at `i` to `x ι_{s,i}`).

**Even payment systems (halved data).** An even payment system on a graded family, with slot type `S`, is given by its **halved data**: functions `p : S → ℕ → A` and `κ : S → S → ℕ → A`. Its payments are `π_s(f) = 2 p_s(f)` and its couplings are `K_{ss'}(f) = 2 κ_{ss'}(f)` (used only for `s > s'`); every value lies in `2A`, which is the paper's evenness. The operator `G = G[fl, F, p, κ] : M^S → M^S` is the `A`-linear map with
  `G(x ι_{s',i}) = (F x) ι_{s'} + 2 p_{s'}(fl i) · x ι_{s',i} + Σ_{s ∈ S, s > s'} 2 κ_{s s'}(fl i) · x ι_{s,i}`
for `s' ∈ S`, `i ∈ ι`, `x ∈ N i` (here `F x` means `F` applied to `x` placed at `i` in `M`).

**The doubling `Φ`.** For a graded family `(ι, fl, N, F)`, its double `Φ` is the graded family with index type `ι × {0, 1}`, floor `fl^Φ(i, e) = 2 fl(i) + e`, modules `N^Φ(i, e) = N i` (the element `x` at `(i, e)` is the paper's `b_e x`), and operator
  `F^Φ(x at (i, 0)) = x at (i, 1)`,  `F^Φ(x at (i, 1)) = 2 · (F x)` placed with `e = 0`
(i.e. `F^Φ(b_0 n) = b_1 n` and `F^Φ(b_1 n) = 2 b_0 (F n)`).

**The twisted data.** From halved data `(p, κ)` on `Φ`, define halved data `(p', κ')` on the original family:
- `p'_s(f) := −p_s(2f) · p_s(2f + 1)`;
- `κ'_{u s'}(f) := −[ p_{s'}(2f + 1) κ_{u s'}(2f) + κ_{u s'}(2f + 1) p_u(2f) + Σ_{s ∈ S, s' < s < u} κ_{s s'}(2f + 1) κ_{u s}(2f) ]`.
These are the halved forms of the paper's `π'_s(f) = −π_s(2f) π_s(2f + 1)/2` and `K'_{us'}(f) = −½[π_{s'}(2f+1) K_{us'}(2f) + K_{us'}(2f+1) π_u(2f) + Σ_{s'<s<u} K_{ss'}(2f+1) K_{us}(2f)]` (with `π = 2p`, `K = 2κ`: `π' = 2p'`, `K' = 2κ'`). So `G' := G[fl, F, p', κ']` is again an even payment system, with no division.

## Part A — the twist move

**Theorem A (the twist move, scaled).** For every graded family `(ι, fl, N, F)`, every slot type `S`, all halved data `(p, κ)` on `Φ` and every `c ∈ A`, there is an `A`-linear isomorphism
  `M_Φ^S / range(c · G_Φ)  ≅  (M^S / c·M^S) × (M^S / range(c · 2 · G'))`,
where `G_Φ := G[fl^Φ, F^Φ, p, κ]` on `M_Φ^S = ⨁_{(s,(i,e))} N i`, and `G' := G[fl, F, p', κ']` on `M^S`. Here `c · G` is the scalar multiple of the operator and `c·M^S` is the submodule `c • ⊤`.

**Corollary A1 (Proposition 4.1).** With `c = 1`: `coker G_Φ ≅ coker(2 G')`, i.e. `M_Φ^S / range G_Φ ≅ M^S / range(2 · G')`.

**Corollary A2 (one move of Proposition 4.3).** With `c = 2^h` (`h ∈ ℕ`): `coker(2^h G_Φ) ≅ (M^S / 2^h M^S) × coker(2^{h+1} G')`.

*Proof (from the paper, scaled).* Write `B_0` and `B_1` for the submodules of `M_Φ^S` spanned by the elements at `(s, (i, 0))` and at `(s, (i, 1))`; `M_Φ^S = B_0 ⊕ B_1`, and `B_e ≅ M^S` by `x at (s, (i, e)) ↦ x ι_{s,i}`. For `x ∈ N i` of floor `f = fl i`,
  `G_Φ(b_0 x ι_{s'}) = b_1 x ι_{s'} + 2p_{s'}(2f) b_0 x ι_{s'} + Σ_{s>s'} 2κ_{ss'}(2f) b_0 x ι_s.`
Let `φ` be the `A`-linear automorphism of `M_Φ^S` that fixes `B_0` and sends `b_1 x ι_{s'}` to the right side above (it is unipotent: identity plus a map `B_1 → B_0`). Then `G_Φ(b_0 x ι_{s'}) = φ(b_1 x ι_{s'})`. Also
  `G_Φ(b_1 x ι_{s'}) = 2 b_0 (F x) ι_{s'} + 2p_{s'}(2f+1) b_1 x ι_{s'} + Σ_{s>s'} 2κ_{ss'}(2f+1) b_1 x ι_s`;
substituting `b_1 y ι_s = φ(b_1 y ι_s) − 2p_s(2f) b_0 y ι_s − Σ_{u>s} 2κ_{us}(2f) b_0 y ι_u` for each `b_1` term gives
  `G_Φ(b_1 x ι_{s'}) = 2 · G'(x ι_{s'})|_{B_0} + (an element of φ(B_1))`,
where `G'(x ι_{s'})|_{B_0}` is `G'(x ι_{s',i})` transported to `B_0`: the coefficient of `b_0 x ι_{s'}` is `−4p_{s'}(2f+1)p_{s'}(2f) = 2·2p'_{s'}(f)`, and that of `b_0 x ι_u` (`u > s'`) is `−4[p_{s'}(2f+1)κ_{us'}(2f) + κ_{us'}(2f+1)p_u(2f) + Σ_{s'<s<u} κ_{ss'}(2f+1)κ_{us}(2f)] = 2·2κ'_{us'}(f)`. Hence
  `range(c · G_Φ) = c·φ(B_1) + c·(2 G')(B_0)`  (inside `B_0 ⊕ φ(B_1)`),
and `φ^{-1}` maps it onto `c·B_1 ⊕ c·2G'(B_0)`. So `M_Φ^S / range(c G_Φ) ≅ B_1/cB_1 ⊕ B_0/range(c·2G') ≅ (M^S/cM^S) × coker(c·2G')`. ∎

## Checks before formalization

`lean/chkC11.py` (log `logs/chkC11.log`): 300 random graded families over `ℤ` (1–3 slots, 1–3 indices with floors ≤ 3 and modules `ℤ^1` or `ℤ^2`, a random integer `F`, random halved data with values in `[−3, 3]`), each with `c ∈ {1, 2, 4, 3, −2}`: the invariant factors over `ℤ` of `c·G_Φ` (computed with `sympy`) equal those of `(ℤ/c)^{rank} ⊕ coker(c·2G')`. 1 500 checks, 0 failures. Controls, each of which must fail somewhere, and does: `κ'` without the middle sum (40); `p_u(2f + 1)` in place of `p_u(2f)` (260); `coker(c·G')` without the factor `2` (1 490); without the summand `(ℤ/c)^{rank}` (1 200).
