module

public import RequestProject.Smith2.PartM
public import RequestProject.Smith2.PartZ
public import RequestProject.Smith2.PartG
public import RequestProject.Conjugation.All

/-!
# `C46_smith_form_and_cokernel_over_Z2.md`, Part V — the entries of `M_w(Ξ)` over `ℤ_2`

(V1) `V1`; (V2) `V2`.

Hypotheses (H) of the file: `1 ≤ l`, `2 ≤ α`, `1 ≤ c`, `η : ℤ_[2]` with `IsUnit η`,
`ζ : ℕ → ℤ → ℤ_[2]`, and `GkZ` with `DanceRel ds 1 (fun _ _ => XiOpZ α c η ζ) GkZ`, where
`ds = Families.ds l`. The reindexing `cs : Fin (2^m) ≃ Fin (Dance.slots ds 1)` of the file is
`Fin.cast (slots_cast ds)` (the cast along `Dance.slots_eq ds 1` and `one_mul`), and
`X s s' = finalM GkZ (cs s) (cs s')` is `(finalM GkZ).submatrix (Fin.cast _) (Fin.cast _)`.
-/

@[expose] public section

noncomputable section

namespace Smith2

open FormalOps FormalDance Windows DanceSmith Matrix Finset

/-- Part V of `C46_smith_form_and_cokernel_over_Z2.md`: the equality `2 ^ m = Dance.slots ds 1`
along which `cs` casts (`Dance.slots_eq ds 1` and
`one_mul`). -/
lemma slots_cast (ds : List Bool) : 2 ^ Dance.mCount ds = Dance.slots ds 1 :=
  ((Dance.slots_eq ds 1).trans (one_mul _)).symm

/-- Proof of (V2) of `C46_smith_form_and_cokernel_over_Z2.md`: an integer with exact power `2^n`
has norm `2^{−n}` in `ℤ_[2]`. -/
lemma norm_int_of_exact {z : ℤ} {n : ℕ} (h1 : (2 : ℤ) ^ n ∣ z) (h2 : ¬ (2 : ℤ) ^ (n + 1) ∣ z) :
    ‖(z : ℤ_[2])‖ = (2 : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨w, rfl⟩ := h1
  have hw : Odd w := by
    rcases Int.even_or_odd w with ⟨v, rfl⟩ | h
    · exact absurd ⟨v, by ring⟩ h2
    · exact h
  have hu := PadicInt.isUnit_iff.1 (FamilyGroup.U1 hw)
  push_cast
  rw [norm_mul, hu, mul_one, norm_pow]
  have : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
    have := PadicInt.norm_p (p := 2); exact_mod_cast this
  rw [this, _root_.zpow_neg, zpow_natCast, inv_pow]

/-- **(V1)** of `C46_smith_form_and_cokernel_over_Z2.md`: under (H), for all `s, s'`,
`X s s' = 0 ↔ ¬ Dset ds s' ⊆ Dset ds s`, and if `Dset ds s' ⊆ Dset ds s` then
`‖X s s'‖ = ‖((Windows.finalMatrix ℤ ds α c s s' : ℤ) : ℤ_[2])‖`, where
`X s s' = finalM GkZ (cs s) (cs s')`. -/
theorem V1 {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℤ_[2]} (hη : IsUnit η)
    (ζ : ℕ → ℤ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => XiOpZ α c η ζ) GkZ)
    (s s' : Fin (2 ^ Dance.mCount (Families.ds l))) :
    (finalM GkZ (Fin.cast (slots_cast _) s) (Fin.cast (slots_cast _) s') = 0 ↔
      ¬ Dset (Families.ds l) s' ⊆ Dset (Families.ds l) s) ∧
    (Dset (Families.ds l) s' ⊆ Dset (Families.ds l) s →
      ‖finalM GkZ (Fin.cast (slots_cast _) s) (Fin.cast (slots_cast _) s')‖ =
        ‖((finalMatrix ℤ (Families.ds l) α c s s' : ℤ) : ℤ_[2])‖) := by
  have hG' := danceRel_map PadicInt.Coe.ringHom (Families.ds l) 1 _ GkZ hG
  have hXi : (Matrix.map (fun _ _ : Fin 1 => XiOpZ α c η ζ) (Bf.map PadicInt.Coe.ringHom)) =
      fun _ _ => PathSum.XiOp α c (η : ℚ_[2]) (fun j f => (ζ j f : ℚ_[2])) := by
    funext a b; exact (M5 α c η ζ).1
  rw [hXi] at hG'
  have hη' : ‖(η : ℚ_[2])‖ = 1 := by rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.1 hη
  have hζ' : ∀ j, 2 ≤ j → ∀ f, ‖((ζ j f : ℤ_[2]) : ℚ_[2])‖ ≤ 1 := fun j _ f => by
    rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one _
  obtain ⟨GSig, -, -, hT2, hF1⟩ := Conjugation.T_eta hl hα hc hη' hζ' _ hG'
  set t := Fin.cast (slots_cast (Families.ds l)) s
  set t' := Fin.cast (slots_cast (Families.ds l)) s'
  have hfin : finalM (GkZ.map (Bf.map PadicInt.Coe.ringHom)) t t' =
      ((finalM GkZ t t' : ℤ_[2]) : ℚ_[2]) := rfl
  obtain ⟨hz, hn⟩ := hT2 t t'
  have hF := hF1 t t'
  rw [hfin] at hz hn
  have hη0 : (η : ℚ_[2]) ≠ 0 := by intro h; rw [h, norm_zero] at hη'; exact zero_ne_one hη'
  have hk := Stability.length_ds_pos hl
  by_cases hsub : Dset (Families.ds l) s' ⊆ Dset (Families.ds l) s
  · have hnest : Stability.nest (Families.ds l) t t' := hsub
    rw [if_pos hnest] at hF
    have hD2 := (theorem_D_ii (Families.ds l) α c (by omega) s s').1 hsub
    have hD3 := (theorem_D_iii (Families.ds l) hk α c (by omega) s s' hsub (by omega)).1
    have hM : ((Deficit.Mc (Ids (Families.ds l)) (Families.ds l).length (α : ℤ) c
        (Dset (Families.ds l) t) (Dset (Families.ds l) t') : ℚ) : ℚ_[2]) =
        ((finalMatrix ℤ (Families.ds l) α c s s' : ℤ) : ℚ_[2]) := by
      change ((Deficit.Mc (Ids (Families.ds l)) (Families.ds l).length (α : ℤ) c
        (Dset (Families.ds l) s) (Dset (Families.ds l) s') : ℚ) : ℚ_[2]) = _
      rw [← hD2]; push_cast; rfl
    rw [hM] at hF
    have hnorm : ‖finalM GSig t t'‖ = ‖((finalMatrix ℤ (Families.ds l) α c s s' : ℤ) : ℤ_[2])‖ := by
      rw [hF, norm_mul, norm_zpow, hη', _root_.one_zpow, one_mul, PadicInt.norm_def]
      push_cast; rfl
    refine ⟨⟨fun h => ?_, fun h => absurd hsub h⟩, fun _ => ?_⟩
    · exfalso
      have h0 : finalM GSig t t' = 0 := hz.1 (by rw [h]; rfl)
      rw [hF] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact zpow_ne_zero _ hη0 h
      · exact hD3 (by exact_mod_cast h)
    · rw [PadicInt.norm_def, hn, hnorm]
  · have hnest : ¬ Stability.nest (Families.ds l) t t' := hsub
    rw [if_neg hnest] at hF
    refine ⟨⟨fun _ => hsub, fun _ => ?_⟩, fun h => absurd h hsub⟩
    exact PadicInt.coe_eq_zero.1 (hz.2 hF)

/-- **(V2)** of `C46_smith_form_and_cokernel_over_Z2.md`: under (H) there is `N₀` such that for
every `N ≥ N₀`, `trunc N X` satisfies the hypothesis of (G1) with `i := c`, and `E j < N` for the
exponents `E` of (G1) (every `E` with `(E j : ℤ) = Cst ds α c + yHat ds α c (2^m − 1 − j)` for
`j < 2^m`), where `X s s' = finalM GkZ (cs s) (cs s')`. -/
theorem V2 {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℤ_[2]} (hη : IsUnit η)
    (ζ : ℕ → ℤ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => XiOpZ α c η ζ) GkZ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∀ s s' : Fin (2 ^ Dance.mCount (Families.ds l)),
        (¬ Dset (Families.ds l) s' ⊆ Dset (Families.ds l) s →
          trunc N ((finalM GkZ).submatrix (Fin.cast (slots_cast _)) (Fin.cast (slots_cast _)))
            s s' = 0) ∧
        (Dset (Families.ds l) s' ⊆ Dset (Families.ds l) s →
          trunc N ((finalM GkZ).submatrix (Fin.cast (slots_cast _)) (Fin.cast (slots_cast _)))
            s s' ≠ 0 ∧
          ∃ n : ℕ, (n : ℤ) = Cst (Families.ds l) α c +
              GoldenMatching.cHat (Families.ds l).length (Ids (Families.ds l)) α (c - 1)
                (Dset (Families.ds l) s) (Dset (Families.ds l) s') ∧
            2 ^ n ∣ trunc N ((finalM GkZ).submatrix (Fin.cast (slots_cast _))
              (Fin.cast (slots_cast _))) s s' ∧
            ¬ 2 ^ (n + 1) ∣ trunc N ((finalM GkZ).submatrix (Fin.cast (slots_cast _))
              (Fin.cast (slots_cast _))) s s')) ∧
      (∀ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount (Families.ds l),
          (E j : ℤ) = Cst (Families.ds l) α c +
            yHat (Families.ds l) α c (2 ^ Dance.mCount (Families.ds l) - 1 - j)) →
        ∀ j < 2 ^ Dance.mCount (Families.ds l), E j < N) := by
  set M := 2 ^ Dance.mCount (Families.ds l)
  have hk := Stability.length_ds_pos hl
  set f1 : Fin M × Fin M → ℕ := fun p =>
    (Cst (Families.ds l) α c + GoldenMatching.cHat (Families.ds l).length (Ids (Families.ds l)) α
      (c - 1) (Dset (Families.ds l) p.1)
      (Dset (Families.ds l) p.2)).toNat
  set f2 : Fin M → ℕ := fun j =>
    (Cst (Families.ds l) α c + yHat (Families.ds l) α c (M - 1 - j)).toNat
  refine ⟨univ.sup f1 + univ.sup f2 + 1, fun N hN => ⟨fun s s' => ?_, fun E hE j hj => ?_⟩⟩
  · set x := finalM GkZ (Fin.cast (slots_cast (Families.ds l)) s)
      (Fin.cast (slots_cast (Families.ds l)) s')
    have hV := V1 hl hα hc hη ζ GkZ hG s s'
    have hZ := Z0 x N
    refine ⟨fun hsub => ?_, fun hsub => ?_⟩
    · show ((x.appr N : ℕ) : ℤ) = 0
      rw [hZ.2.1 (hV.1.2 hsub)]; rfl
    · obtain ⟨-, n, hn, h1, h2⟩ := (G2 (Families.ds l) hk α c (by omega) hc s s').2 hsub
      have hnorm : ‖x‖ = (2 : ℝ) ^ (-(n : ℤ)) := by
        rw [hV.2 hsub]; exact norm_int_of_exact h1 h2
      have hx0 : x ≠ 0 := fun h => hV.1.1 h hsub
      have hnN : n < N := by
        have : n = f1 (s, s') := by simp only [f1]; rw [← hn, Int.toNat_natCast]
        have hle : f1 (s, s') ≤ univ.sup f1 := le_sup (mem_univ _)
        omega
      obtain ⟨g1, g2, g3⟩ := hZ.2.2 n hx0 hnorm hnN
      exact ⟨g1, n, hn, g2, g3⟩
  · have : E j = f2 ⟨j, hj⟩ := by simp only [f2]; rw [← hE j hj, Int.toNat_natCast]
    have hle : f2 ⟨j, hj⟩ ≤ univ.sup f2 := le_sup (mem_univ _)
    omega

end Smith2
