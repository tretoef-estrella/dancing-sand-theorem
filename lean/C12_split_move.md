# The split move (Proposition 4.2, §4.2)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), Proposition 4.2 (the split move), with the basis `A_n, B_n, C_n, Dd_n` of `V ⊗ Φ(N')`. As in piece C11, the statement is proved over **any commutative ring `A`** and in a **scaled form**, `coker(c·G)` for every `c ∈ A`; the paper's Proposition 4.2 is the case `c = 1`, and `c = 2^h` is what the proof of Proposition 4.3 uses.

This file reuses, without changing them, piece C11 (`RequestProject/Payment/`): graded families `(ι, fl, N, F)`, slot types, `Payment.Sys`, `slotLof`, `slotEmb`, the payment system `Payment.G fl F p κ` (halved data), and the twisted data `Payment.pT`, `Payment.κT`.

## Setting

`A` is a commutative ring; `(ι, fl, N, F)` is a graded family as in C11; `M := ⨁_{i∈ι} N i`; `S` is a slot type (finite, linearly ordered).

**The tensor model `V ⊗ Φ`.** The graded family `VΦ` has index type `ι × {0,1} × {0,1}`, floor `fl^{VΦ}(i, e, e') = 2 fl(i) + e + e'`, module `N i` at `(i, e, e')` (the element `x` at `(i, e, e')` is the paper's `b_e ⊗ b_{e'} x`), and operator `F^{VΦ} = F_V ⊗ 1 + 1 ⊗ F^Φ`, i.e. on `x` at `(i, e, e')`:
- the `F_V` part: `x` at `(i, 1, e')` if `e = 0`, and `0` if `e = 1`  (`F_V b_0 = b_1`, `F_V b_1 = 0`);
- the `F^Φ` part: `x` at `(i, e, 1)` if `e' = 0`, and `2·(F x)` placed at `(·, e, 0)` if `e' = 1`  (`F^Φ b_0 n = b_1 n`, `F^Φ b_1 n = 2 b_0 F n`).

**The split model `Ψ`.** The graded family `Ψ` has index type `ι × {A, B, C, Dd}` (encode `{A, B, C, Dd}` as `Fin 4`), floors `fl^Ψ(i, A) = 2 fl(i)`, `fl^Ψ(i, B) = fl^Ψ(i, C) = 2 fl(i) + 1`, `fl^Ψ(i, Dd) = 2 fl(i) + 2`, module `N i` at each `(i, j)`, and operator, on `x ∈ N i`,
  `F^Ψ(A x) = B x + 2·C x`,  `F^Ψ(B x) = 2·A(F x)`,  `F^Ψ(C x) = Dd x`,  `F^Ψ(Dd x) = 2·C(F x)`,
where `J x` denotes `x` placed at `(i, J)` and `J(F x)` denotes `F x ∈ M` placed with label `J`.

**The change of basis.** `θ : M_{VΦ} → M_Ψ` is the `A`-linear map with, on `x ∈ N i`,
  `θ(b_0 b_0 x) = A x`,  `θ(b_0 b_1 x) = B x + C x`,  `θ(b_1 b_0 x) = C x`,  `θ(b_1 b_1 x) = Dd x`
(so `A = b_0b_0`, `B = b_0b_1 − b_1b_0`, `C = b_1b_0`, `Dd = b_1b_1`). It preserves floors.

**The split data.** From halved data `(p, κ)` on `Ψ` with slot type `S`, define halved data `(p'', κ'')` on the original family with slot type `S × {A, C}`, ordered lexicographically with `A` before `C` (encode as `Lex (S × Fin 2)`, `0 = A`, `1 = C`):
- `p''_{(s,A)}(f) := −p_s(2f) p_s(2f+1)`,  `p''_{(s,C)}(f) := −p_s(2f+1) p_s(2f+2)`;
- for `u > s'`: `κ''_{(u,A),(s',A)}(f) := −[p_{s'}(2f+1) κ_{us'}(2f) + κ_{us'}(2f+1) p_u(2f) + Σ_{s'<s<u} κ_{ss'}(2f+1) κ_{us}(2f)]` (the twisted coupling of C11 at the floors `(2f, 2f+1)`);
- for `u > s'`: `κ''_{(u,C),(s',C)}(f) := −[p_{s'}(2f+2) κ_{us'}(2f+1) + κ_{us'}(2f+2) p_u(2f+1) + Σ_{s'<s<u} κ_{ss'}(2f+2) κ_{us}(2f+1)]` (the same at the floors `(2f+1, 2f+2)`);
- `κ''_{(s',C),(s',A)}(f) := −p_{s'}(2f+1)`;
- for `u > s'`: `κ''_{(u,C),(s',A)}(f) := −κ_{us'}(2f+1)`;
- all other values are `0` (in particular there is no coupling from a slot `C` to a slot `A`).
These are the halved forms of the paper's `π''`, `K''` (`π = 2p`, `K = 2κ`). The value of `κ''` on pairs that are not of the form «larger slot, smaller slot» is never used by `Payment.G`.

## Part A — the change of basis

**(A1)** `θ` is an `A`-linear equivalence `M_{VΦ} ≅ M_Ψ` (its inverse sends `A x ↦ b_0b_0 x`, `B x ↦ b_0b_1 x − b_1b_0 x`, `C x ↦ b_1b_0 x`, `Dd x ↦ b_1b_1 x`).
**(A2)** `θ ∘ F^{VΦ} = F^Ψ ∘ θ`.
**(A3)** For every slot type `S` and all halved data `(p, κ)`, the slotwise map `θ_S : Sys_{VΦ} → Sys_Ψ` (apply `θ` in each slot) is an `A`-linear equivalence with `θ_S ∘ G[fl^{VΦ}, F^{VΦ}, p, κ] = G[fl^Ψ, F^Ψ, p, κ] ∘ θ_S`. Consequently, for every `c ∈ A`, `coker(c·G_{VΦ}) ≅ coker(c·G_Ψ)`.

*Proof.* (A1): the two maps are inverse on generators. (A2): on `b_0b_0 x`: `F^{VΦ} = b_1b_0 x + b_0b_1 x ↦ C x + B x + C x = B x + 2 C x = F^Ψ(A x)`; on `b_0b_1 x`: `b_1b_1 x + 2 b_0b_0 F x ↦ Dd x + 2 A F x`, and `F^Ψ(B x + C x) = 2 A F x + Dd x`; on `b_1b_0 x`: `b_1b_1 x ↦ Dd x = F^Ψ(C x)`; on `b_1b_1 x`: `2 b_1b_0 F x ↦ 2 C F x = F^Ψ(Dd x)`. (A3): `θ` maps floor `g` to floor `g` (both `b_0b_1 x` and `b_1b_0 x` have floor `2fl(i)+1`, as `B x` and `C x`), so it commutes with the payments and the couplings, and with `F` by (A2). ∎

## Part B — the split move

**Theorem B (the split move, scaled).** For every graded family, slot type `S`, halved data `(p, κ)` on `Ψ` and `c ∈ A`, there is an `A`-linear isomorphism
  `Sys_Ψ / range(c · G_Ψ)  ≅  (M^S / c M^S) × (M^S / c M^S) × (M^{S×{A,C}} / range(c · 2 · G''))`,
where `G_Ψ := G[fl^Ψ, F^Ψ, p, κ]` on `Sys_Ψ = ⨁_{(s,(i,j))} N i`, `M^S = ⨁_{(s,i)} N i`, and `G'' := G[fl, F, p'', κ'']` on `M^{S×{A,C}} = ⨁_{((s,X), i)} N i` with the lexicographic slot order.

**Corollary B1 (Proposition 4.2).** With `c = 1`: `coker G_Ψ ≅ coker(2 G'')`; and, by (A3), `coker G_{VΦ} ≅ coker(2 G'')`.

**Corollary B2 (one split move of Proposition 4.3).** With `c = 2^h`: `coker(2^h G_Ψ) ≅ (M^S/2^h M^S)^2 × coker(2^{h+1} G'')`.

*Proof (from the paper, scaled).* For `x ∈ N i` of floor `f`,
  `G_Ψ(A x ι_{s'}) = B x ι_{s'} + 2 C x ι_{s'} + 2p_{s'}(2f) A x ι_{s'} + Σ_{s>s'} 2κ_{ss'}(2f) A x ι_s`,
  `G_Ψ(C x ι_{s'}) = Dd x ι_{s'} + 2p_{s'}(2f+1) C x ι_{s'} + Σ_{s>s'} 2κ_{ss'}(2f+1) C x ι_s`.
The unipotent automorphism `φ` fixing the `A`- and `C`-parts and sending `B x ι_{s'}`, `Dd x ι_{s'}` to these right sides satisfies `G_Ψ(A x ι) = φ(B x ι)`, `G_Ψ(C x ι) = φ(Dd x ι)`. Substituting `B y ι_s = φ(B y ι_s) − 2C y ι_s − 2p_s(2f) A y ι_s − Σ_{u>s} 2κ_{us}(2f) A y ι_u` and `Dd y ι_s = φ(Dd y ι_s) − 2p_s(2f+1) C y ι_s − Σ_{u>s} 2κ_{us}(2f+1) C y ι_u` into
  `G_Ψ(B x ι_{s'}) = 2 A(F x) ι_{s'} + 2p_{s'}(2f+1) B x ι_{s'} + Σ_{s>s'} 2κ_{ss'}(2f+1) B x ι_s` and
  `G_Ψ(Dd x ι_{s'}) = 2 C(F x) ι_{s'} + 2p_{s'}(2f+2) Dd x ι_{s'} + Σ_{s>s'} 2κ_{ss'}(2f+2) Dd x ι_s`
gives `2·G''(x ι_{(s',A)})` and `2·G''(x ι_{(s',C)})` under `A y ι_s ↦ y ι_{(s,A)}`, `C y ι_s ↦ y ι_{(s,C)}`, plus elements of `φ(span of B, Dd)`: the `A`-coefficients are those of C11 at `(2f, 2f+1)`; the `C`-coefficients in `G_Ψ(B x ι_{s'})` are `−4p_{s'}(2f+1)` at `s'` and `−4κ_{ss'}(2f+1)` at `s > s'`; in `G_Ψ(Dd x ι_{s'})` there is no `A`-term and the `C`-coefficients are those of C11 at `(2f+1, 2f+2)`. So `range(c G_Ψ) = c·φ(B ⊕ Dd) + c·2G''(A ⊕ C)`, and `φ^{-1}` gives `Sys_Ψ / range(c G_Ψ) ≅ (B ⊕ Dd)/c(B ⊕ Dd) ⊕ (A ⊕ C)/range(c·2G'')`; the `B` and `Dd` parts are each `≅ M^S`, and `A ⊕ C ≅ M^{S×{A,C}}`. ∎

## Checks before formalization

`lean/chkC12.py` (log `logs/chkC12.log`): 150 random graded families over `ℤ` (1–2 slots, 1–2 indices with floors ≤ 3 and modules `ℤ^1` or `ℤ^2`, random integer `F` and halved data in `[−3, 3]`), each with `c ∈ {1, 2, 4, 3, −2}`: the invariant factors over `ℤ` (sympy) of `c·G_Ψ` equal those of `c·G_{VΦ}` (750 checks of (A3)) and those of `(ℤ/c)^{2·rank} ⊕ coker(c·2·G'')` (750 checks of Theorem B). 0 failures. Controls, each of which must fail somewhere, and does: no coupling `(s',A) → (u,C)` (35); the `C`–`C` couplings at the floors `(2f, 2f+1)` (75); without the factor `2` (745); one copy of `M^S/cM^S` instead of two (600); `+p_{s'}(2f+1)` for the coupling `(s',A) → (s',C)` (25).
