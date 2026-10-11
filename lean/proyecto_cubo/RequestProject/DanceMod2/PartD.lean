module

public import RequestProject.DanceMod2.PartM

/-!
# `C50b_the_dance_modulo_two.md`: Part D — Lemma 10.18 for the dance

(D0) congruent coefficient functions give congruent covariant systems (`MCong 1`); (D1) Lemma 10.18:
the dances of two good congruent systems run side by side (`GlueDance.PairRel`), by induction on
`ds` exactly as C48b (T2); (D2) the glued dance, by C50 (D1), (D2); (D3) the glue datum `Z`.
-/

@[expose] public section

noncomputable section

namespace DanceMod2

open Cleanliness FormalOps FormalDance ContZero Finset
open RingK (covSys Dn oS)

/-- **(D0)** of `C50b_the_dance_modulo_two.md`: for every `P h c`, every type `n` and every
`e : n → Dn P`: `Cong2 Γ Γ'' →
MCong 1 (fun j j' => covSys P h c Γ'' (e j) (e j')) (fun j j' => covSys P h c Γ (e j) (e j'))`. -/
theorem D0 (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) {n : Type*} (e : n → Dn P)
    (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    Cong2 Γ Γ'' →
      MCong 1 (fun j j' => covSys P h c Γ'' (e j) (e j'))
        (fun j j' => covSys P h c Γ (e j) (e j')) := by
  intro hc
  choose z hz using hc
  refine ⟨fun j j' => ⟨fun m f => if (e j').1 ⊆ (e j).1 then
    -z ((e j).1 \ (e j').1) m ((2 : ℤ_[2]) ^ h * f + oS (e j).1 + c) else 0⟩, ?_⟩
  intro s s' m f _
  simp only [Matrix.sub_apply, Bf.coef_sub, RingK.covSys_coef, Matrix.smul_apply, Bf.coef_smul,
    pow_one]
  split_ifs
  · linear_combination -(hz ((e s).1 \ (e s').1) m ((2 : ℤ_[2]) ^ h * f + oS (e s).1 + c))
  · simp

/-- **(D1) Lemma 10.18** of `C50b_the_dance_modulo_two.md`: for every `ds : List Bool`, `r h : ℕ`,
`P : Finset ℕ` with `∀ t ∈ P, t < h`, `c : ℤ_[2]`, `Γ Γ''` with `Good Γ`, `Good Γ''`,
`Cong2 Γ Γ''`, every `e : Fin r ≃ Dn P` and `X Y` with
`hX : X = fun j j' => covSys P h c Γ (e j) (e j')` and
`hY : Y = fun j j' => covSys P h c Γ'' (e j) (e j')`: `∃ Xk Yk, GlueDance.PairRel ds r X Y Xk Yk`. -/
theorem D1 (ds : List Bool) (r h : ℕ) (P : Finset ℕ) (hP : ∀ t ∈ P, t < h) (c : ℤ_[2])
    (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'') (hc : Cong2 Γ Γ'')
    (e : Fin r ≃ Dn P) (X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hX : X = fun j j' => covSys P h c Γ (e j) (e j'))
    (hY : Y = fun j j' => covSys P h c Γ'' (e j) (e j')) :
    ∃ Xk Yk, GlueDance.PairRel ds r X Y Xk Yk := by
  induction ds generalizing r h P Γ Γ'' X Y with
  | nil =>
    refine ⟨X, Y, ?_, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
    subst hX hY
    exact D0 P h c e Γ Γ'' hc
  | cons d rest ih =>
    have hm : MCong 1 Y X := by subst hX hY; exact D0 P h c e Γ Γ'' hc
    cases d with
    | false =>
      obtain ⟨Γ', Γ''', hG', hG''', hc', hC1, hC2⟩ := M5 Γ Γ'' hΓ hΓ'' hc P h c
      have hC1' := L1 e _ _ hC1
      have hC2' := L1 e _ _ hC2
      rw [← hX] at hC1'
      rw [← hY] at hC2'
      obtain ⟨Xk, Yk, hk⟩ := ih r (h + 1) P (fun t ht => Nat.lt_succ_of_lt (hP t ht)) Γ' Γ'''
        hG' hG''' hc' e _ _ rfl rfl
      exact ⟨Xk, Yk, hm, _, _, hC1', hC2', hk⟩
    | true =>
      have hhP : h ∉ P := fun hh => lt_irrefl h (hP h hh)
      obtain ⟨Γ', Γ''', hG', hG''', hc', hC1, hC2⟩ := M6 Γ Γ'' hΓ hΓ'' hc P h c hhP
      have hC1' := L1 (Equiv.prodCongr e (Equiv.refl (Fin 2))) _ _ hC1
      have hC2' := L1 (Equiv.prodCongr e (Equiv.refl (Fin 2))) _ _ hC2
      have hVX : vsplit X = fun q q' =>
          vsplit (covSys P h c Γ) ((Equiv.prodCongr e (Equiv.refl (Fin 2))) q)
            ((Equiv.prodCongr e (Equiv.refl (Fin 2))) q') := by
        rw [hX, DanceXi.T1]; rfl
      have hVY : vsplit Y = fun q q' =>
          vsplit (covSys P h c Γ'') ((Equiv.prodCongr e (Equiv.refl (Fin 2))) q)
            ((Equiv.prodCongr e (Equiv.refl (Fin 2))) q') := by
        rw [hY, DanceXi.T1]; rfl
      rw [← hVX] at hC1'
      rw [← hVY] at hC2'
      let e₂ : Fin (r * 2) ≃ Dn (insert h P) :=
        ((Dance.splitIso r).symm.toEquiv.trans ofLex).trans
          ((Equiv.prodCongr e (Equiv.refl (Fin 2))).trans (splitDn P h hhP))
      have hP' : ∀ t ∈ insert h P, t < h + 1 := fun t ht => by
        rcases mem_insert.1 ht with rfl | ht
        · exact Nat.lt_succ_self t
        · exact Nat.lt_succ_of_lt (hP t ht)
      obtain ⟨Xk, Yk, hk⟩ := ih (r * 2) (h + 1) (insert h P) hP' Γ' Γ''' hG' hG''' hc' e₂
        _ _ rfl rfl
      exact ⟨Xk, Yk, hm, _, _, hC1', hC2', hk⟩

/-- **(D2) The glued dance** of `C50b_the_dance_modulo_two.md`: under the hypotheses of (D1), for
every `r₂` with `hr : r₂ = 2 * r` and every `Z` with `MAgree (Y - X) ((2 : ℤ_[2]) • Z)`, there are
`Xk Yk Zk` with `DanceRel ds r X Xk`, `DanceRel ds r Y Yk`, `MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)`
and `DanceRel ds r₂ (GlueDance.glueC hr X Y Z) (GlueDance.glueC (GlueDance.S4 ds hr) Xk Yk Zk)`. -/
theorem D2 (ds : List Bool) (r h : ℕ) (P : Finset ℕ) (hP : ∀ t ∈ P, t < h) (c : ℤ_[2])
    (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'') (hc : Cong2 Γ Γ'')
    (e : Fin r ≃ Dn P) (X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hX : X = fun j j' => covSys P h c Γ (e j) (e j'))
    (hY : Y = fun j j' => covSys P h c Γ'' (e j) (e j'))
    (r₂ : ℕ) (hr : r₂ = 2 * r) (Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hZ : MAgree (Y - X) ((2 : ℤ_[2]) • Z)) :
    ∃ Xk Yk Zk, DanceRel ds r X Xk ∧ DanceRel ds r Y Yk ∧
      MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk) ∧
      DanceRel ds r₂ (GlueDance.glueC hr X Y Z) (GlueDance.glueC (GlueDance.S4 ds hr) Xk Yk Zk) := by
  obtain ⟨Xk, Yk, hk⟩ := D1 ds r h P hP c Γ Γ'' hΓ hΓ'' hc e X Y hX hY
  obtain ⟨h1, h2, -⟩ := GlueDance.D1 ds hk
  obtain ⟨Zk, h3, h4⟩ := GlueDance.D2 ds hr hk Z hZ
  exact ⟨Xk, Yk, Zk, h1, h2, h3, h4⟩

/-- **(D3)** of `C50b_the_dance_modulo_two.md`: under the hypotheses of (D1), there is `Z` with
`MAgree (Y - X) ((2 : ℤ_[2]) • Z)`. (Of the hypotheses of (D1), only `Cong2 Γ Γ''`, `hX` and `hY`
are used; the word `ds`, `∀ t ∈ P, t < h`, `Good Γ` and `Good Γ''` are kept, as anonymous binders,
as in the file.) -/
theorem D3 (_ : List Bool) (r h : ℕ) (P : Finset ℕ) (_ : ∀ t ∈ P, t < h) (c : ℤ_[2])
    (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (_ : Good Γ) (_ : Good Γ'') (hc : Cong2 Γ Γ'')
    (e : Fin r ≃ Dn P) (X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hX : X = fun j j' => covSys P h c Γ (e j) (e j'))
    (hY : Y = fun j j' => covSys P h c Γ'' (e j) (e j')) :
    ∃ Z, MAgree (Y - X) ((2 : ℤ_[2]) • Z) := by
  obtain ⟨Z, hZ⟩ := D0 P h c e Γ Γ'' hc
  subst hX hY
  exact ⟨Z, by simpa only [pow_one] using hZ⟩

end DanceMod2
