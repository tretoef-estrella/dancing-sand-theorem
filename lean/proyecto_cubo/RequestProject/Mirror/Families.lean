module

public import RequestProject.PodiumCor.All

/-!
# `C37_the_mirror_that_doubles.md`: Part A — Lemma 9.8 (the families of `N' + 1`, `N'` odd)

Namespace `Mirror`.  Nothing of the Setting is redefined: C31 `FamDec.L`, `FamDec.m`, `Vdot`;
C32 `Families.ds`; C14 `Windows.Ids`; C13 `Dance.mCount`; C7 `TheoremF.dancer`; C3 `Rulers.h`,
`Rulers.t1`, `Rulers.hSum`; C36 `PodiumCor.smallExps` are used directly.
-/

@[expose] public section

namespace Mirror

open Finset Families

/-! ### (A1) -/

/-- **(A1)** of `C37_the_mirror_that_doubles.md` (first item): for odd `N'`, every element of
`FamDec.L N'` is odd.  From C31 (M3). -/
theorem A1_odd (N' : ℕ) (hN : N' % 2 = 1) : ∀ lam ∈ FamDec.L N', lam % 2 = 1 := by
  intro lam h
  have := FamDec.M3 N' (by omega) lam h
  omega

/-- `l.flatMap Vdot = l.map (· + 1)` for a list of odd numbers (auxiliary for (A1) of
`C37_the_mirror_that_doubles.md`). -/
lemma flatMap_Vdot_odd (l : List ℕ) (hl : ∀ x ∈ l, x % 2 = 1) :
    l.flatMap FamDec.Vdot = l.map (· + 1) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.map_cons, ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))]
    obtain ⟨j, rfl⟩ : ∃ j, x = 2 * j + 1 := ⟨x / 2, by have := hl x (by simp); omega⟩
    rw [FamDec.Vdot_odd]
    rfl

/-- **(A1)** of `C37_the_mirror_that_doubles.md` (second item): for odd `N'`,
`FamDec.L (N' + 1) = (FamDec.L N').map (· + 1)`.  From (A1, first item), `Vdot_odd` and
`L_succ`. -/
theorem A1_map (N' : ℕ) (hN : N' % 2 = 1) : FamDec.L (N' + 1) = (FamDec.L N').map (· + 1) := by
  rw [FamDec.L_succ, flatMap_Vdot_odd _ (A1_odd N' hN)]

/-- **(A1)** of `C37_the_mirror_that_doubles.md` (multiplicities): for odd `N'` and every `μ`,
`FamDec.m (μ + 1) (N' + 1) = FamDec.m μ N'`. -/
theorem A1_m_succ (N' : ℕ) (hN : N' % 2 = 1) (μ : ℕ) :
    FamDec.m (μ + 1) (N' + 1) = FamDec.m μ N' := by
  unfold FamDec.m
  rw [A1_map N' hN, List.count_map_of_injective _ _ (add_left_injective 1)]

/-- **(A1)** of `C37_the_mirror_that_doubles.md` (multiplicities): for odd `N'`,
`FamDec.m 0 (N' + 1) = 0`. -/
theorem A1_m_zero (N' : ℕ) (hN : N' % 2 = 1) : FamDec.m 0 (N' + 1) = 0 := by
  unfold FamDec.m
  rw [A1_map N' hN, List.count_eq_zero]
  simp

/-- **(A1)** of `C37_the_mirror_that_doubles.md` (Lemma 9.8, all items together): for odd `N'`,
every element of `L N'` is odd, `L (N' + 1) = (L N').map (· + 1)`,
`m (μ + 1) (N' + 1) = m μ N'` for every `μ`, and `m 0 (N' + 1) = 0`. -/
theorem A1 (N' : ℕ) (hN : N' % 2 = 1) :
    (∀ lam ∈ FamDec.L N', lam % 2 = 1) ∧ FamDec.L (N' + 1) = (FamDec.L N').map (· + 1) ∧
      (∀ μ, FamDec.m (μ + 1) (N' + 1) = FamDec.m μ N') ∧ FamDec.m 0 (N' + 1) = 0 :=
  ⟨A1_odd N' hN, A1_map N' hN, A1_m_succ N' hN, A1_m_zero N' hN⟩

/-! ### (A2) -/

/-- **(A2)** of `C37_the_mirror_that_doubles.md`: for odd `λ`,
`(ds (λ + 1)).length = (ds λ).length`. -/
theorem A2_length (lam : ℕ) (hlam : lam % 2 = 1) : (ds (lam + 1)).length = (ds lam).length := by
  obtain ⟨l, rfl⟩ : ∃ l, lam = 2 * l + 1 := ⟨lam / 2, by omega⟩
  rw [show 2 * l + 1 + 1 = 2 * l + 2 by ring, ds_even, ds_odd]
  rfl

/-- **(A2)** of `C37_the_mirror_that_doubles.md`: for odd `λ`, `0 ∉ Windows.Ids (ds λ)`. -/
theorem A2_zero_notMem (lam : ℕ) (hlam : lam % 2 = 1) : 0 ∉ Windows.Ids (ds lam) := by
  obtain ⟨l, rfl⟩ : ∃ l, lam = 2 * l + 1 := ⟨lam / 2, by omega⟩
  rw [ds_odd, Windows.Ids_cons]
  simp

/-- **(A2)** of `C37_the_mirror_that_doubles.md`: for odd `λ`,
`Windows.Ids (ds (λ + 1)) = insert 0 (Windows.Ids (ds λ))`. -/
theorem A2_Ids (lam : ℕ) (hlam : lam % 2 = 1) :
    Windows.Ids (ds (lam + 1)) = insert 0 (Windows.Ids (ds lam)) := by
  obtain ⟨l, rfl⟩ : ∃ l, lam = 2 * l + 1 := ⟨lam / 2, by omega⟩
  rw [show 2 * l + 1 + 1 = 2 * l + 2 by ring, ds_even, ds_odd, Windows.Ids_cons,
    Windows.Ids_cons]
  ext t; simp

/-- **(A2)** of `C37_the_mirror_that_doubles.md`: for odd `λ`,
`Dance.mCount (ds (λ + 1)) = Dance.mCount (ds λ) + 1`. -/
theorem A2_mCount (lam : ℕ) (hlam : lam % 2 = 1) :
    Dance.mCount (ds (lam + 1)) = Dance.mCount (ds lam) + 1 := by
  obtain ⟨l, rfl⟩ : ∃ l, lam = 2 * l + 1 := ⟨lam / 2, by omega⟩
  rw [show 2 * l + 1 + 1 = 2 * l + 2 by ring, ds_even, ds_odd]
  rfl

/-- For odd `λ`, `|Ids (ds (λ + 1))| = |Ids (ds λ)| + 1` (consequence of (A2) of
`C37_the_mirror_that_doubles.md`). -/
theorem A2_card (lam : ℕ) (hlam : lam % 2 = 1) :
    (Windows.Ids (ds (lam + 1))).card = (Windows.Ids (ds lam)).card + 1 := by
  rw [A2_Ids lam hlam, card_insert_of_notMem (A2_zero_notMem lam hlam)]

/-- **(A2)** of `C37_the_mirror_that_doubles.md` (Lemma 9.8, all items together): for odd `λ`,
`(ds (λ + 1)).length = (ds λ).length`, `0 ∉ Ids (ds λ)`,
`Ids (ds (λ + 1)) = insert 0 (Ids (ds λ))` and `mCount (ds (λ + 1)) = mCount (ds λ) + 1`. -/
theorem A2 (lam : ℕ) (hlam : lam % 2 = 1) :
    (ds (lam + 1)).length = (ds lam).length ∧ 0 ∉ Windows.Ids (ds lam) ∧
      Windows.Ids (ds (lam + 1)) = insert 0 (Windows.Ids (ds lam)) ∧
        Dance.mCount (ds (lam + 1)) = Dance.mCount (ds lam) + 1 :=
  ⟨A2_length lam hlam, A2_zero_notMem lam hlam, A2_Ids lam hlam, A2_mCount lam hlam⟩

/-! ### (A3) -/

/-- The rank of `t ∈ I` in `insert 0 I` is its rank in `I` plus one (auxiliary for (A3) of
`C37_the_mirror_that_doubles.md`). -/
lemma card_filter_insert_zero {I : Finset ℕ} (h0 : 0 ∉ I) {t : ℕ} (ht : t ∈ I) :
    ((insert 0 I).filter (· < t)).card = (I.filter (· < t)).card + 1 := by
  have htpos : 0 < t := Nat.pos_of_ne_zero fun h => h0 (h ▸ ht)
  rw [filter_insert, if_pos htpos, card_insert_of_notMem (fun h => h0 (mem_filter.1 h).1)]

/-- `bit (r + 1) (2q + b) = bit r q` for `b < 2` (auxiliary for (A3) of
`C37_the_mirror_that_doubles.md`). -/
lemma bit_succ_two_mul (r q b : ℕ) (hb : b < 2) :
    Houses.bit (r + 1) (2 * q + b) = Houses.bit r q := by
  unfold Houses.bit
  rw [pow_succ', ← Nat.div_div_eq_div_mul, show (2 * q + b) / 2 = q by omega]

/-- The common computation behind (A3) of `C37_the_mirror_that_doubles.md`: for `0 ∉ I` and
`b < 2`, `dancer (insert 0 I) (2q + b)` is `dancer I q ∪ {0}` if `b = 1` and `dancer I q` if
`b = 0`. -/
lemma dancer_insert_zero (I : Finset ℕ) (h0 : 0 ∉ I) (q b : ℕ) (hb : b < 2) :
    TheoremF.dancer (insert 0 I) (2 * q + b) =
      if b = 1 then insert 0 (TheoremF.dancer I q) else TheoremF.dancer I q := by
  ext t
  unfold TheoremF.dancer
  by_cases ht0 : t = 0
  · subst ht0
    have hr : ((insert 0 I).filter (· < 0)).card = 0 := by simp
    simp only [mem_filter, mem_insert, true_or, true_and, hr]
    unfold Houses.bit
    split_ifs with hb1
    · subst hb1; simp
    · have : b = 0 := by omega
      subst this; simp [h0]
  · simp only [mem_filter, mem_insert, ht0, false_or]
    constructor
    · rintro ⟨ht, hbit⟩
      rw [card_filter_insert_zero h0 ht, bit_succ_two_mul _ _ _ hb] at hbit
      split_ifs <;> simp [ht, hbit, ht0]
    · intro h
      have h' : t ∈ I ∧ Houses.bit (I.filter (· < t)).card q = 1 := by
        split_ifs at h
        · simpa [ht0] using h
        · simpa using h
      refine ⟨h'.1, ?_⟩
      rw [card_filter_insert_zero h0 h'.1, bit_succ_two_mul _ _ _ hb]
      exact h'.2

/-- **(A3)** of `C37_the_mirror_that_doubles.md`: for every finite set `I` with `0 ∉ I` and every
`q`, `TheoremF.dancer (insert 0 I) (2 * q) = TheoremF.dancer I q`. -/
theorem A3_even (I : Finset ℕ) (h0 : 0 ∉ I) (q : ℕ) :
    TheoremF.dancer (insert 0 I) (2 * q) = TheoremF.dancer I q := by
  simpa using dancer_insert_zero I h0 q 0 (by norm_num)

/-- **(A3)** of `C37_the_mirror_that_doubles.md`: for every finite set `I` with `0 ∉ I` and every
`q`, `TheoremF.dancer (insert 0 I) (2 * q + 1) = insert 0 (TheoremF.dancer I q)`. -/
theorem A3_odd (I : Finset ℕ) (h0 : 0 ∉ I) (q : ℕ) :
    TheoremF.dancer (insert 0 I) (2 * q + 1) = insert 0 (TheoremF.dancer I q) := by
  simpa using dancer_insert_zero I h0 q 1 (by norm_num)

/-- **(A3)** of `C37_the_mirror_that_doubles.md` (both items together). -/
theorem A3 (I : Finset ℕ) (h0 : 0 ∉ I) (q : ℕ) :
    TheoremF.dancer (insert 0 I) (2 * q) = TheoremF.dancer I q ∧
      TheoremF.dancer (insert 0 I) (2 * q + 1) = insert 0 (TheoremF.dancer I q) :=
  ⟨A3_even I h0 q, A3_odd I h0 q⟩

/-! ### (A4) -/

/-- **(A4)** of `C37_the_mirror_that_doubles.md`: for odd `λ`,
`PodiumCor.smallExps (λ + 1) = PodiumCor.smallExps λ + PodiumCor.smallExps λ`. -/
theorem A4 (lam : ℕ) (hlam : lam % 2 = 1) :
    PodiumCor.smallExps (lam + 1) = PodiumCor.smallExps lam + PodiumCor.smallExps lam := by
  unfold PodiumCor.smallExps
  rw [A2_length lam hlam, A2_card lam hlam, ← sum_add_distrib]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_Ico] at ha
  rw [show (Windows.Ids (ds lam)).card + 1 + (ds lam).length - 1 - a =
      ((Windows.Ids (ds lam)).card + (ds lam).length - 1 - a) + 1 by omega, pow_succ, mul_two,
    Multiset.replicate_add]

/-! ### (A5) -/

/-- `min (insert k I) = min I` when `I ⊆ {0, …, k − 1}` (with the convention `min ∅ = k`;
auxiliary for (A5) of `C37_the_mirror_that_doubles.md`). -/
lemma minOr_insert_self {k : ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) :
    Rulers.minOr k (insert k I) = Rulers.minOr k I := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · rw [Rulers.minOr_empty]
    exact Rulers.minOr_eq_of_mem (by simp) (by simp)
  · have hm := Rulers.minOr_mem (k := k) hne
    refine Rulers.minOr_eq_of_mem (mem_insert_of_mem hm) fun x hx => ?_
    rcases mem_insert.1 hx with rfl | hx
    · exact (hI _ hm).le
    · exact Rulers.minOr_le hx

/-- **(A5)** of `C37_the_mirror_that_doubles.md`, first item: if `0 ∉ I`, then
`Rulers.h k (insert 0 I) t = Rulers.h k I t` for every `t ∈ I`.  (The hypothesis
`I ⊆ range k` of the file is not needed for this item.) -/
theorem A5_h (k : ℕ) (I : Finset ℕ) (h0 : 0 ∉ I) {t : ℕ} (ht : t ∈ I) :
    Rulers.h k (insert 0 I) t = Rulers.h k I t := by
  have htpos : 0 < t := Nat.pos_of_ne_zero fun h => h0 (h ▸ ht)
  unfold Rulers.h Rulers.next
  congr 2
  ext u
  simp only [mem_filter, mem_insert]
  constructor
  · rintro ⟨h | h | h, hu⟩
    · exact ⟨Or.inl h, hu⟩
    · omega
    · exact ⟨Or.inr h, hu⟩
  · rintro ⟨h | h, hu⟩
    · exact ⟨Or.inl h, hu⟩
    · exact ⟨Or.inr (Or.inr h), hu⟩

/-- **(A5)** of `C37_the_mirror_that_doubles.md`, second item: if `I ⊆ range k` and `0 ∉ I`, then
`Rulers.h k (insert 0 I) 0 = Rulers.t1 k I`. -/
theorem A5_h_zero (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (h0 : 0 ∉ I) :
    Rulers.h k (insert 0 I) 0 = Rulers.t1 k I := by
  have hI' : ∀ t ∈ I, t < k := fun t ht => mem_range.1 (hI ht)
  unfold Rulers.h Rulers.next Rulers.t1
  rw [Nat.sub_zero]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : I = ∅ := eq_empty_of_forall_notMem fun t ht => by have := hI' t ht; omega
    subst this
    simp [Rulers.minOr]
  · have hf : (insert k (insert 0 I)).filter (fun u => 0 < u) = insert k I := by
      ext u
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨h | h | h, hu⟩
        · exact Or.inl h
        · omega
        · exact Or.inr h
      · rintro (h | h)
        · exact ⟨Or.inl h, by omega⟩
        · exact ⟨Or.inr (Or.inr h), Nat.pos_of_ne_zero fun h' => h0 (h' ▸ h)⟩
    rw [hf, minOr_insert_self hI']

/-- **(A5)** of `C37_the_mirror_that_doubles.md`, third item: if `0 ∉ I` and `D ⊆ I`, then
`Rulers.hSum k (insert 0 I) D = Rulers.hSum k I D`.  (The hypothesis `I ⊆ range k` of the file
is not needed for this item.) -/
theorem A5_hSum (k : ℕ) (I : Finset ℕ) (h0 : 0 ∉ I) {D : Finset ℕ} (hD : D ⊆ I) :
    Rulers.hSum k (insert 0 I) D = Rulers.hSum k I D :=
  sum_congr rfl fun _ ht => A5_h k I h0 (hD ht)

/-- **(A5)** of `C37_the_mirror_that_doubles.md`, fourth item: if `I ⊆ range k`, `0 ∉ I` and
`D ⊆ I`, then `Rulers.hSum k (insert 0 I) (insert 0 D) = Rulers.hSum k I D + Rulers.t1 k I`. -/
theorem A5_hSum_insert (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (h0 : 0 ∉ I) {D : Finset ℕ}
    (hD : D ⊆ I) :
    Rulers.hSum k (insert 0 I) (insert 0 D) = Rulers.hSum k I D + Rulers.t1 k I := by
  have h0D : 0 ∉ D := fun h => h0 (hD h)
  rw [Rulers.hSum, sum_insert h0D, ← Rulers.hSum, A5_hSum k I h0 hD, A5_h_zero k I hI h0,
    add_comm]

/-- **(A5)** of `C37_the_mirror_that_doubles.md` (all items together): if `I ⊆ range k` and
`0 ∉ I`, then `h' t = h t` for `t ∈ I`, `h' 0 = t₁`, and for `D ⊆ I`, `h'(D) = h(D)` and
`h'(D ∪ {0}) = h(D) + t₁` (where `h'` is computed for `insert 0 I`). -/
theorem A5 (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (h0 : 0 ∉ I) :
    (∀ t ∈ I, Rulers.h k (insert 0 I) t = Rulers.h k I t) ∧
      Rulers.h k (insert 0 I) 0 = Rulers.t1 k I ∧
      ∀ D ⊆ I, Rulers.hSum k (insert 0 I) D = Rulers.hSum k I D ∧
        Rulers.hSum k (insert 0 I) (insert 0 D) = Rulers.hSum k I D + Rulers.t1 k I :=
  ⟨fun _ ht => A5_h k I h0 ht, A5_h_zero k I hI h0,
    fun _ hD => ⟨A5_hSum k I h0 hD, A5_hSum_insert k I hI h0 hD⟩⟩

end Mirror
