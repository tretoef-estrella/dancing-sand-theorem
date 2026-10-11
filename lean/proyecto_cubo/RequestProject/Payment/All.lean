module

public import RequestProject.Payment.Basic
public import RequestProject.Payment.Block
public import RequestProject.Payment.Twist
public import RequestProject.Payment.TheoremA

/-!
# Payment systems and the twist move (`C11_payment_systems_twist.md`)

Index of the formalization (namespace `Payment`).  Everything is over an arbitrary commutative
ring `A`.

## Encodings

* **Graded family** `(ι, fl, N, F)`: `ι` a type with `[DecidableEq ι]`, `fl : ι → ℕ`,
  `N : ι → Type*` with `[∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]`, and
  `F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)` (`DirectSum`, so elements have finite support).  No
  hypothesis on `F` (as in the file).
* **Slot type** `S`: `[Fintype S] [LinearOrder S]`.
* **Module of a system** `M^S`: `Sys N S = ⨁ q : S × ι, N q.2`.  `x ι_{s,i}` is
  `slotLof A N S s i x` (`= DirectSum.lof A (S × ι) _ (s, i) x`); `m ι_s` is
  `slotEmb A N S s m`.
* **Payment system with halved data** `p : S → ℕ → A`, `κ : S → S → ℕ → A`:
  `G fl F p κ`, defined by `DirectSum.toModule` on generators by
  `x ι_{s',i} ↦ (F x) ι_{s'} + (2 * p s' (fl i)) • x ι_{s',i}
     + Σ_{s ∈ univ.filter (s' < ·)} (2 * κ s s' (fl i)) • x ι_{s,i}`.
* **Double `Φ`**: index type `ι × Fin 2`, floor `flΦ fl (i, e) = 2 * fl i + e`, modules
  `NΦ N (i, e) = N i`, operator `FΦ F` (`x at (i,0) ↦ x at (i,1)`,
  `x at (i,1) ↦ 2 • (F x placed with e = 0)`).  So `M_Φ^S = Sys (NΦ N) S` and
  `G_Φ = G (flΦ fl) (FΦ F) p κ`.
* **Twisted data**: `pT p` (`p'`) and `κT p κ` (`κ'`), exactly the formulas of the Setting (no
  division); `G' = G fl F (pT p) (κT p κ)`.
* `c · G` is the scalar multiple `c • G` of linear maps; `c·M^S` is the pointwise
  `c • (⊤ : Submodule A (Sys N S))`; quotients are `Submodule` quotients `⧸`.
* "There is an `A`-linear isomorphism" is `Nonempty (_ ≃ₗ[A] _)`.

## Files

* `Basic.lean` — the Setting: `Sys`, `slotLof`, `slotEmb`, `G`, `NΦ`, `flΦ`, `embΦ`, `FΦ`,
  `pT`, `κT`.
* `Block.lean`, `Twist.lean` — the steps of the *Proof* of Theorem A (the decomposition
  `B_0 ⊕ B_1`, the block form of `G_Φ`, the coefficient identity behind `p'`, `κ'`, and the
  row/column reduction).
* `TheoremA.lean` — **Theorem A** `theorem_A`, **Corollary A1** `corollary_A1`,
  **Corollary A2** `corollary_A2`.

## Remarks

* The statements are exactly those of the file, over any commutative ring `A` and any `c ∈ A`.
* No hypothesis is unused; in particular, nothing about `F` (e.g. that it raises the floor by
  one) is assumed, as the file says.
* Corollary A2's right-hand factor is written `range ((2 : A) ^ (h + 1) • G')`, i.e.
  `coker(2^{h+1} G')`, as in the file.
-/
