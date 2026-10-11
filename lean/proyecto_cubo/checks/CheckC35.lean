import RequestProject.Podium.All

/-! Auditor's check file for Lean piece C35, the podium arithmetic (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C35_the_podium_arithmetic.md`: ψ, P_l, t_{l+1}, Y_l, clear unfolded by `rfl`;
(P0); Lemma 9.2 (La)–(Ld); Lemma 9.5 (K); steps (M1)–(M5) of Proposition 9.6; hand values; then
`#print axioms`. -/

open Finset

-- The encodings, unfolded.
example (k : ℕ) (I E : Finset ℕ) :
    Podium.psi k I E = ∑ t ∈ E, ((Rulers.h k I t : ℤ) - 2 ^ t) := rfl
example (I : Finset ℕ) (l : ℕ) :
    Podium.P I l = I.filter (fun t => (I.filter (· < t)).card < l) := rfl
example (k : ℕ) (I : Finset ℕ) (l : ℕ) :
    Podium.tAt k I l = Rulers.minOr k (I \ Podium.P I l) := rfl
example (k : ℕ) (I : Finset ℕ) (l : ℕ) :
    Podium.Y k I l = 2 ^ k + Rulers.oE (I \ Podium.P I l) := rfl
example (N q : ℕ) : Podium.clear N q = 2 ^ q * (N / 2 ^ q) := rfl
-- Hand values: I = {0, 2}, k = 3: P_1 = {0}, Y_1 = 8 + 4 = 12, clear 13 2 = 12.
example : Podium.P {0, 2} 1 = {0} := by decide
example : Podium.Y 3 {0, 2} 1 = 12 := by decide
example : Podium.clear 13 2 = 12 := by decide

-- (P0).
example (k : ℕ) (I : Finset ℕ) (l : ℕ) (hl : l ≤ I.card) :
    Podium.P I l ⊆ I ∧ (Podium.P I l).card = l ∧
      (∀ t ∈ Podium.P I l, ∀ u ∈ I \ Podium.P I l, t < u) ∧
      Podium.P I 0 = ∅ ∧ Podium.P I I.card = I ∧
      Podium.Y k I l + Rulers.oE (Podium.P I l) = Rulers.lam k I + 1 := Podium.P0 k I l hl

-- Lemma 9.2.
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (l : ℕ) :
    Rulers.phi (Rulers.lam k I + 1) + Podium.psi k I (Podium.P I l) = Rulers.phi (Podium.Y k I l) ∧
      Rulers.v2 (Podium.Y k I l) = Podium.tAt k I l := Podium.La hI l
example (N q : ℕ) : Podium.clear N q ≤ N := Podium.Lb_le N q
example (N y : ℕ) (hy : 1 ≤ y) (hyN : y ≤ N) :
    ∃ q, 1 ≤ Podium.clear N q ∧ Rulers.phi y ≤ Rulers.phi (Podium.clear N q) := Podium.Lb N y hy hyN
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (l : ℕ) :
    ∃ q, Podium.Y k I l = Podium.clear (Rulers.lam k I + 1) q := Podium.Lc_Y_eq_clear hI l
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (q : ℕ)
    (h : 1 ≤ Podium.clear (Rulers.lam k I + 1) q) :
    ∃ l ≤ I.card, Podium.clear (Rulers.lam k I + 1) q = Podium.Y k I l := Podium.Lc_clear_eq_Y hI q h
example (k : ℕ) (I : Finset ℕ) (l : ℕ) (hl : 1 ≤ l) : Podium.Y k I l ≤ Podium.Y k I 1 :=
  Podium.Lc_Y_le_Y_one l hl
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (hs : 1 ≤ I.card) (q : ℕ)
    (h : 1 ≤ Podium.clear (Podium.Y k I 1) q) :
    ∃ l, 1 ≤ l ∧ l ≤ I.card ∧ Podium.clear (Podium.Y k I 1) q = Podium.Y k I l :=
  Podium.Lc_clear_Y_one hI hs q h
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (y : ℕ) (hy : 1 ≤ y)
    (hyN : y ≤ Rulers.lam k I + 1) : ∃ l ≤ I.card, Rulers.phi y ≤ Rulers.phi (Podium.Y k I l) :=
  Podium.Ld hI y hy hyN
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (hs : 1 ≤ I.card) (y : ℕ) (hy : 1 ≤ y)
    (hyN : y ≤ Podium.Y k I 1) :
    ∃ l, 1 ≤ l ∧ l ≤ I.card ∧ Rulers.phi y ≤ Rulers.phi (Podium.Y k I l) :=
  Podium.Ld_one hI hs y hy hyN

-- Lemma 9.5 (Lemma K).
example (a B q : ℕ) (hB : 1 ≤ B) : ∃ y, 1 ≤ y ∧ y ≤ 2 ^ q * (a + B) ∧
    Rulers.phi (2 ^ q * B) + Rulers.kappa a B ≤ Rulers.phi y := Podium.K a B q hB

-- Steps (M), (K) of Proposition 9.6.
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (D : Finset ℕ) (hD : D ⊆ I) (i : ℕ) (hi : 1 ≤ i) :
    Rulers.clock k I i D = Rulers.phi (Rulers.lam k I + 1) + 2 * Podium.psi k I D +
      Rulers.kappa (i - 1) (2 ^ k + Rulers.oE (I \ D)) - Rulers.kappa (i - 1) (Rulers.oE D) :=
  Podium.M1 hI hD i hi
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (l i : ℕ) (hi : 1 ≤ i) :
    ∑ D ∈ (Podium.P I l).powerset, Rulers.clock k I i D =
      ∑ D ∈ (Podium.P I l).powerset, (Rulers.phi (Podium.Y k I l) +
        Rulers.kappa (i - 1) (Podium.Y k I l + Rulers.oE D) - Rulers.kappa (i - 1) (Rulers.oE D)) :=
  Podium.M2 hI l i hi
example (Y o m q : ℕ) (hY : 2 ^ q ∣ Y) (ho : o < 2 ^ q) :
    Rulers.kappa m (Y + o) - Rulers.kappa m o =
      Rulers.kappa (m / 2 ^ q + (if 2 ^ q ≤ m % 2 ^ q + o then 1 else 0)) (Y / 2 ^ q) :=
  Podium.M3 Y o m q hY ho
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (l : ℕ) (D : Finset ℕ) (hD : D ⊆ Podium.P I l)
    (m : ℕ) : ∃ y, 1 ≤ y ∧ y ≤ Rulers.lam k I + 1 + m ∧
      Rulers.phi (Podium.Y k I l) + Rulers.kappa m (Podium.Y k I l + Rulers.oE D) -
        Rulers.kappa m (Rulers.oE D) ≤ Rulers.phi y := Podium.M4 hI l hD m
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) (l : ℕ) (hl : l ≤ I.card) (i : ℕ) (hi : 1 ≤ i)
    (G : ℤ) (hG : ∀ y : ℕ, 1 ≤ y → y ≤ Rulers.lam k I + 1 + (i - 1) → Rulers.phi y ≤ G) :
    ∑ D ∈ (Podium.P I l).powerset, Rulers.clock k I i D ≤ 2 ^ l * G :=
  Podium.M5 hI l hl i hi G hG

#print axioms Podium.P0
#print axioms Podium.La
#print axioms Podium.Lb_le
#print axioms Podium.Lb
#print axioms Podium.Lc_Y_eq_clear
#print axioms Podium.Lc_clear_eq_Y
#print axioms Podium.Lc_Y_le_Y_one
#print axioms Podium.Lc_clear_Y_one
#print axioms Podium.Ld
#print axioms Podium.Ld_one
#print axioms Podium.K
#print axioms Podium.M1
#print axioms Podium.M2
#print axioms Podium.M3
#print axioms Podium.M4
#print axioms Podium.M5
