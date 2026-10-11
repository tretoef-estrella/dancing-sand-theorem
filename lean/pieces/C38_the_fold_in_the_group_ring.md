# C38 — the fold in the group ring: Lemma 10.1 and Corollary 10.2 (module form)

Piece C38 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §10.1). Folder
`RequestProject/Fold/`, namespace `Fold`. The folders C1–C37 are certified: do not change them.

## Setting (reuse, do not redefine)

- C17 `CubeLaplacian`: `G n := Fin n → ZMod 2`, `e n i`, `lap A n` (`(lap A n f) g = n·f g − Σ_i f (g + e n i)`), `coker`, `K`, `Syl2`.
- C18 `DPLattice`: `DPLattice A`, `Hop`, `H`, `Hom`, `tensorPow A n`, `pt`, `wt_pt`, `Tn A n = Fd 1 + n − H`, `psi A n : (G n → A) ≃ₗ[A] ((tensorPow A n).ι → A)`, `psi_comm` (`psi ∘ lap = Tn ∘ psi`), `bvec`, `slice`, `tensorFd`.
- C20 `Doubling.Iso`, `Iso.trans`, `Iso.symm` (C20/D3); C25 `LemmaW.IsWtPres`, `LemmaW.P1` (over a domain of characteristic zero every `Hom` is weight-preserving).
- C29 `Filt.T`, `Filt.tpow`; C30 `Step36.dsumList` and its lemmas; C31 `FamDec.L`, `FamDec.m`, `FamDec.D2`, `FamDec.Z1_D2`; C32 `Families.Q0` (`tpow A n = tensorPow A n`), `Families.Q1`.

## Definitions (new)

- `aElt n : G n := fun _ => 1` (the antipode `a = x_1 ⋯ x_n`).
- `transl A n : (G n → A) →ₗ[A] (G n → A)`, `(transl A n f) g = f (g + aElt n)`.
- `foldSub A n : Submodule A (G n → A) := LinearMap.range (lap A n) ⊔ LinearMap.range (transl A n − 1)`.
- `Gbar n := G n ⧸ AddSubgroup.zmultiples (aElt n)` (the vertex set of the folded cube), with `mk : G n → Gbar n`.
- `lapBar A n : (Gbar n → A) →ₗ[A] (Gbar n → A)`, `(lapBar A n u) x = n·u x − Σ_i u (x + mk (e n i))` (the Laplacian of the folded cube, edges counted with multiplicity).
- `cokerBar n := (Gbar n → ℤ) ⧸ LinearMap.range (lapBar ℤ n)`, `KBar n := Submodule.torsion ℤ (cokerBar n)` (the critical group `K̄(n)`, defined as `K` is in C17).
- `push A n : (G n → A) →ₗ[A] (Gbar n → A)`, `(push A n f) x = Σ_{g : mk g = x} f g`.
- For a DP-lattice `M` over `A`, `c : ℤ`, `B : ℕ`:
  - `signOp M c : Module.End A (M.ι → A)`, `(signOp M c f) i = (−1) ^ ((c − M.wt i) / 2).natAbs * f i`;
  - `expF M B := Σ_{r ∈ range B} M.Fd r`;
  - `aOp M c B := signOp M c ∘ₗ expF M B`;
  - `tauOp M c := M.Fd 1 + (c : A) • 1 − H M`;
  - `Xbar M c B := (M.ι → A) ⧸ (LinearMap.range (tauOp M c) ⊔ LinearMap.range (aOp M c B − 1))`.

On a summand `T(λ)` of `V^{⊗n}` at shift `i = (n − λ)/2`, the centre `c = n` gives `(n − wt)/2 = D + i` and `tauOp = F + 2(D + i) = τ_i`; so `Xbar (T λ) n (n + 1)` is the paper's `X̄(λ, i)`.

## Part G — the fold in the group ring (every commutative ring `A`, every `n`)

**(G1)** `transl A n ∘ₗ transl A n = 1` and `transl A n ∘ₗ lap A n = lap A n ∘ₗ transl A n`.

**(G2)** `push A n` is surjective; `LinearMap.ker (push A n) = LinearMap.range (transl A n − 1)`; `push A n ∘ₗ lap A n = lapBar A n ∘ₗ push A n`.

**(G3)** `(Gbar n → A) ⧸ LinearMap.range (lapBar A n) ≃ₗ[A] (G n → A) ⧸ foldSub A n` (induced by `push`). In particular `cokerBar n ≃ₗ[ℤ] (G n → ℤ) ⧸ foldSub ℤ n`.

*Sketch.* `aElt n + aElt n = 0`, so the coset of `g` is `{g, g + aElt n}` (one element when `n = 0`). `push` is surjective (put the value on one representative); `push f = 0` iff `f (g + a) = −f g` on every coset of size two (and `f g = 0` on a coset of size one), i.e. `f = transl h − h` with `h` supported on representatives. `mk (g + e n i) = mk g + mk (e n i)`.

## Part L — Lemma 10.1 (the antipode on `V^{⊗n}`)

**(L0)** For every `n` and `r > n`, `(tensorPow A n).Fd r = 0`.

**(L1)** For every commutative ring `A` and every `n`:
`(psi A n).toLinearMap ∘ₗ transl A n = aOp (tensorPow A n) n (n + 1) ∘ₗ (psi A n).toLinearMap`.

**(L2)** For `B ≥ n + 1`, `expF (tensorPow A n) B = expF (tensorPow A n) (n + 1)`.

*Sketch.* Induction on `n` along the recursion of `psi` (`gSplit`, `shear`, `sliceEquiv`) and of `tensorFd`. On `V`: `psi` sends `f` to the slots `(f 0 + f 1, −f 1)`, `transl` swaps `f 0, f 1`, and `aOp (V) 1 2` maps the slots `(s_0, s_1)` to `(s_0, −s_0 − s_1)`. `exp(F)` is group-like for `tensorFd` (`F^{(r)}(b_0 ⊗ m) = b_0 ⊗ F^{(r)} m + b_1 ⊗ F^{(r−1)} m`, `F^{(r)}(b_1 ⊗ m) = b_1 ⊗ F^{(r)} m`), and so is the sign `(−1)^{#b_1}`; the weight of `pt A n S` is `n − 2|S|` (C18 `wt_pt`). (L0) from (W): `F^{(r)}` lowers the weight by `2r`, and the weights of `tensorPow A n` lie in `[−n, n]`.

**(L3)** (transport) Let `u : Doubling.Iso M N` with `IsWtPres u.hom.toLin` and `IsWtPres u.inv.toLin`. Then `u.hom.toLin` intertwines `expF M B` with `expF N B`, `signOp M c` with `signOp N c`, `aOp M c B` with `aOp N c B`, and `tauOp M c` with `tauOp N c`; hence `Xbar M c B ≃ₗ[A] Xbar N c B`. Over a domain of characteristic zero the weight hypotheses hold for every iso (C25 `P1`).

**(L4)** (direct sums) For every list `Ls`, the equivalence of C32 (Q1), `((dsumList Ls).ι → A) ≃ₗ[A] Π_{j : Fin Ls.length} (Ls.get j).ι → A`, intertwines `Fd r` (every `r`), `H`, `signOp`, `expF`, `aOp`, `tauOp` componentwise; hence `Xbar (dsumList Ls) c B ≃ₗ[A] Π_j Xbar (Ls.get j) c B`.

## Part C — Corollary 10.2, module form

**(C1)** Under the hypotheses of C30 (A1) (`H1 φ`, `H2 φ`, `H3 A`, `OneAddTwoUnit A`, `(2 : B) = 0`, with `[IsDomain A] [CharZero A] [OddUnits A]`), for every `n`:
`(G n → A) ⧸ foldSub A n ≃ₗ[A] Π_{j : Fin (FamDec.L n).length} Xbar (Filt.T A ((FamDec.L n).get j)) n (n + 1)`.

**(C2)** For `A = ℤ_[2]` (hypotheses from C28 `Lift2.Z1`, C21 `Twist.C3_hyp`), for every `n`:
`(G n → ℤ_[2]) ⧸ foldSub ℤ_[2] n ≃ₗ[ℤ_[2]] Π_{j : Fin (FamDec.L n).length} Xbar (Filt.T ℤ_[2] ((FamDec.L n).get j)) n (n + 1)`.

*Sketch.* `psi` is an equivalence with `psi ∘ lap = Tn ∘ psi` (C18) and `psi ∘ transl = aOp ∘ psi` (L1), and `Tn A n = tauOp (tensorPow A n) n`; so `(G n → A) ⧸ foldSub ≃ Xbar (tensorPow A n) n (n + 1)`. Then `tensorPow = tpow` (C32 Q0), Theorem 3.6 (C31 D2) with (L3) and (L4).

*Not in this piece (C38b):* the folded cube has `cokerBar n ≃ ℤ × KBar n` (it is connected; the sum of the values), the group form `ℤ_[2] × Syl2 (KBar n) ≅ ⊕ X̄(λ, (n−λ)/2)^{m_λ(n)}` of Corollary 10.2, and Proposition 10.3.

## Checks done before sending

- Brute force (`chkC38.py`, in exactly these coordinates: `G n`, `lap`, `psi`, `tensorFd`): (L0) `n ≤ 6`; (L1), (L2) and `psi ∘ lap = Tn ∘ psi`, 25 random `f` for each `n ≤ 6`; (G1), (G2) 15 random `f` for each `n ≤ 6`; and for `n = 1..6` the integer Smith forms of `(G n → ℤ)/foldSub`, of `V^{⊗n}/(range Tn + range (aOp − 1))` and of `cokerBar n`, which agree (free rank 1). As a sanity check, the 2-parts of `K̄(n)` equal `2·Syl_2 K(Q_n)` (the fold law) for `n ≤ 6`. 977 checks, 0 failures.
- Controls (each fires): (L1) with the factors swapped (`expF ∘ signOp`: 148 of 150 random cases differ), without the sign (147 of 150), with `B = n` (145 of 150); (C) translation by `e n 0` instead of `aElt n` (differs for every `n ≥ 2`); `aOp` without the sign (differs for every `n ≥ 3`).

## Instructions

Encodings are your choice provided they are faithful; say in a docstring how each object is encoded. Keep the statements exactly as in this file (more general statements are fine if noted; say if a hypothesis is unused). Every docstring should name the part of `C38_the_fold_in_the_group_ring.md` it corresponds to. No `sorry`, no new axiom, no `native_decide`.
