module

public import RequestProject.Split.Basic
public import RequestProject.Split.ChangeOfBasis
public import RequestProject.Split.Block
public import RequestProject.Split.Decomp
public import RequestProject.Split.SplitData
public import RequestProject.Split.TheoremB

/-!
# The split move (`C12_split_move.md`)

Index of the formalization (namespace `Split`).  Everything is over an arbitrary commutative
ring `A`, and reuses unchanged, from `C11_payment_systems_twist.md` (`RequestProject/Payment/`):
graded families `(ι, fl, N, F)`, slot types `S` (`[Fintype S] [LinearOrder S]`), `Payment.Sys`,
`Payment.slotLof`, `Payment.slotEmb`, the payment system `Payment.G fl F p κ` (halved data) and the
twisted data `Payment.pT`, `Payment.κT`.

## Encodings (`Basic.lean`, the *Setting*)

* **Tensor model `V ⊗ Φ`**: index type `ι × Fin 2 × Fin 2` (the element `x` at `(i, e, e')` is
  `b_e ⊗ b_{e'} x`), modules `NVΦ N (i, e, e') = N i`, floor `flVΦ fl (i,e,e') = 2 fl(i) + e + e'`,
  operator `FVΦ F = F_V ⊗ 1 + 1 ⊗ F^Φ`, defined on generators with `DirectSum.toModule`.
* **Split model `Ψ`**: index type `ι × Fin 4` (`0 = A`, `1 = B`, `2 = C`, `3 = Dd`), modules
  `NΨ N (i, j) = N i`, floor `flΨ fl (i, j) = 2 fl(i) + ![0, 1, 1, 2] j`, operator `FΨ F`
  (`A x ↦ B x + 2 C x`, `B x ↦ 2 A(F x)`, `C x ↦ Dd x`, `Dd x ↦ 2 C(F x)`), defined on generators
  with `DirectSum.toModule`.
* **Change of basis** `theta` (`θ`), defined on generators (`b_0b_0 x ↦ A x`,
  `b_0b_1 x ↦ B x + C x`, `b_1b_0 x ↦ C x`, `b_1b_1 x ↦ Dd x`), its inverse `thetaInv`, and the
  slotwise maps `thetaS S`, `thetaInvS S` (apply `θ` in each slot).
* **Split data**: slot type `Lex (S × Fin 2)` (`0 = A`, `1 = C`, lexicographic order),
  `pSp p` (`p''`) and `κSp p κ` (`κ''`, which is `0` on the pairs not listed), with no division.
* Systems: `G_Ψ = G (flΨ fl) (FΨ F) p κ` on `Sys (NΨ N) S`, `G_{VΦ} = G (flVΦ fl) (FVΦ F) p κ` on
  `Sys (NVΦ N) S`, `G'' = G fl F (pSp p) (κSp p κ)` on `Sys N (Lex (S × Fin 2))`.
  `c · G` is `c • G` and `c M^S` is `c • ⊤`.

## Results

* **(A1)** `A1_theta_thetaInv`, `A1_thetaInv_theta`, the equivalence `thetaEquiv` and
  `A1_thetaEquiv_coe` (its underlying map is `θ`).
* **(A2)** `A2_theta_comp_F`: `θ ∘ F^{VΦ} = F^Ψ ∘ θ`.
* **(A3)** `thetaSEquiv` and `A3_thetaSEquiv_coe` (`θ_S` is an equivalence),
  `A3_thetaS_comp_G` (`θ_S ∘ G_{VΦ} = G_Ψ ∘ θ_S` for all halved data) and `A3_coker`
  (`coker(c G_{VΦ}) ≅ coker(c G_Ψ)` for every `c`).
* **Theorem B** `theorem_B`, **Corollary B1** `corollary_B1` (for `Ψ`) and `corollary_B1_VΦ`
  (for `V ⊗ Φ`), **Corollary B2** `corollary_B2`.

## Proof files

* `Block.lean`: the row/column reduction on `X⁴` (`blk4CokerEquiv`).
* `Decomp.lean`: `Sys_Ψ ≃ A ⊕ B ⊕ C ⊕ Dd` and `G_Ψ` in block form (`projΨ_comp_G`).
* `SplitData.lean`: the values of `p''`, `κ''`, `M^{S×{A,C}} ≃ A ⊕ C` and `G''` in block form
  (`proj2_comp_G`).
-/
