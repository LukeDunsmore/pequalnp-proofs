import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1452 : ∀ (n f k w : ℕ) (L : Finset (Fin n)) (c : Fin f → Fin n → Fin k) (T : Fin f → Fin k → (Fin n → Bool) → Bool), (∀ S : Finset (Fin n), S.card ≤ w → ∃ j0 : Fin f, Set.InjOn (c j0) (S : Set (Fin n))) → (∀ (j1 : Fin f) (a1 : Fin k) (u v : Fin n → Bool), u ≤ v → T j1 a1 u ≤ T j1 a1 v) → (∀ (j2 : Fin f) (a2 : Fin k) (z : Fin n → Bool), (∀ p2 : Fin n, z p2 = true → c j2 p2 ≠ a2) → T j2 a2 z = false) → (∀ (j3 : Fin f) (a3 : Fin k) (y : Fin n → Bool) (p3 : Fin n), y p3 = true → c j3 p3 = a3 → (∀ q3 : Fin n, y q3 = true → c j3 q3 = a3 → q3 = p3) → (T j3 a3 y = true ↔ p3 ∈ L)) → ∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ w → ((∀ j : Fin f, ∃ a : Fin k, T j a x = true) ↔ ∃ p : Fin n, x p = true ∧ p ∈ L) := by
  classical
  intro n f k w L c T hsplit hmono hzero hone x hx
  constructor
  · intro h
    obtain ⟨j, hj⟩ := hsplit (Finset.univ.filter (fun i : Fin n => x i = true)) hx
    obtain ⟨a, ha⟩ := h j
    have hex : ∃ p : Fin n, x p = true ∧ c j p = a := by
      by_contra hn
      have hz := hzero j a x (by
        intro p hp hcp
        exact hn ⟨p, hp, hcp⟩)
      simp [ha] at hz
    obtain ⟨p, hp, hcp⟩ := hex
    refine ⟨p, hp, (hone j a x p hp hcp ?_).mp ha⟩
    intro q hq hcq
    apply hj (by simpa using hq) (by simpa using hp)
    exact hcq.trans hcp.symm
  · rintro ⟨p, hp, hL⟩ j
    let y : Fin n → Bool := fun q => decide (q = p)
    have hy : y p = true := by simp [y]
    have huniq : ∀ q : Fin n, y q = true → c j q = c j p → q = p := by
      intro q hq _
      simpa [y] using hq
    have ht : T j (c j p) y = true := (hone j (c j p) y p hy rfl huniq).mpr hL
    have hle : y ≤ x := by
      intro q
      by_cases hqp : q = p
      · subst q
        simp [y, hp]
      · simp [y, hqp]
    refine ⟨c j p, ?_⟩
    have hm := hmono j (c j p) y x hle
    exact (Bool.le_iff_imp.mp hm) ht
