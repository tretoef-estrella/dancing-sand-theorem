module

public import RequestProject.OddParts.PartF
public import RequestProject.OddParts.Transport

/-!
# `C52_odd_parts.md`: Part B — Bai's odd part

* (B0) `B0`, (B1) `B1` (Bai's form).
-/

@[expose] public section

noncomputable section

namespace OddParts

open CubeLaplacian Finset

/-- **(B0)** of `C52_odd_parts.md`: for every `n` and every prime `p ≠ 2`,
`Syl_p K(Q_n) ≃+ Syl_p (Π_{S ≠ ∅} ℤ/(2|S|))`. -/
theorem B0 (n : ℕ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (Sylp p (CubeLaplacian.K n) ≃+
      Sylp p ((S : {S : Finset (Fin n) // S.Nonempty}) → ZMod (2 * S.1.card))) := by
  obtain ⟨t⟩ := sylpQuotTransfer (LinearMap.range (CubeLaplacian.L n))
    (LinearMap.range (diagD n)) (fourier n) (ifourier n)
    (by rintro _ ⟨f, rfl⟩; exact ⟨fourier n f, (F1 n f).symm⟩)
    (by rintro _ ⟨v, rfl⟩; exact ⟨ifourier n v, F2 n v⟩)
    (2 ^ n) (F3 n).1 (F3 n).2 p hp (not_dvd_two_pow_of_ne hp hp2 n)
  obtain ⟨d⟩ := sylpDiagQuot (fun S : Finset (Fin n) => 2 * S.card) (diagD n)
    (fun v S => by simp [diagD]) (fun S => S.Nonempty)
    (fun S hS => by simp [Finset.not_nonempty_iff_eq_empty.mp hS]) hp.ne_zero
  exact ⟨(sylpProdBotLeft p ℤ (K n) (sylp_int_eq_bot hp.ne_zero)).symm.trans
    ((sylpCongr p (cokerEquivK n).toAddEquiv).symm.trans (t.trans d))⟩

/-- **(B1)** of `C52_odd_parts.md` (Bai's form): for every `n` and every prime `p ≠ 2`,
`Syl_p K(Q_n) ≃+ Syl_p (⊕_{j=1}^{n} (ℤ/j)^{C(n,j)})`, with `j + 1` for `j : Fin n`. -/
theorem B1 (n : ℕ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (Sylp p (CubeLaplacian.K n) ≃+
      Sylp p ((j : Fin n) → Fin (n.choose (j + 1)) → ZMod (j + 1))) := by
  obtain ⟨b0⟩ := B0 n p hp hp2
  obtain ⟨t⟩ := sylpTwoMul (fun S : {S : Finset (Fin n) // S.Nonempty} => S.1.card) hp hp2
  have r := piZModReindex (idxB n) (fun S : {S : Finset (Fin n) // S.Nonempty} => S.1.card)
    (fun x => x.1 + 1) (idxB_card n)
  have c := (LinearEquiv.piCurry ℤ (fun (j : Fin n) (_ : Fin (n.choose (j + 1))) =>
    ZMod (j + 1))).toAddEquiv
  exact ⟨b0.trans (t.trans (sylpCongr p (r.trans c)))⟩

end OddParts
