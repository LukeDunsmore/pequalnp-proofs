import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1504 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (t : Fin N → (Fin N → Bool) → Bool), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → (∀ l0 : Fin N, Monotone (t l0)) → (∀ (x y : Fin N → Bool), (∀ l1 : Fin N, (Finset.univ.filter (fun p1 : Fin N => I p1 l1 ∧ x p1 = true)).card ≤ 2) → (∃ l2 : Fin N, y l2 = true ∧ t l2 x = true) → ∃ p3 l3 : Fin N, I p3 l3 ∧ x p3 = true ∧ y l3 = true) → (∀ p4 l4 : Fin N, I p4 l4 → ∃ l5 : Fin N, decide (l5 = l4) = true ∧ t l5 (fun k4 : Fin N => decide (k4 = p4)) = true) → ∀ (l6 : Fin N) (z : Fin N → Bool), (∀ l7 : Fin N, (Finset.univ.filter (fun p7 : Fin N => I p7 l7 ∧ z p7 = true)).card ≤ 2) → (t l6 z = true ↔ ∃ p8 : Fin N, I p8 l6 ∧ z p8 = true) := by
  intro N I _ t _ mono sound pairs l z hz
  constructor
  · intro ht
    obtain ⟨p,l',hi,hx,hy⟩ := sound z (fun k => decide (k = l)) hz ⟨l,by simp,ht⟩
    have he : l' = l := of_decide_eq_true hy
    subst l'
    exact ⟨p,hi,hx⟩
  · rintro ⟨p,hi,hp⟩
    obtain ⟨l',he,ht⟩ := pairs p l hi
    have hel : l' = l := of_decide_eq_true he
    subst l'
    have hs : (fun k : Fin N => decide (k = p)) ≤ z := by
      intro k
      change decide (k = p) ≤ z k
      by_cases hk : k = p
      · subst k; simp [hp]
      · simp [hk]
    exact (Bool.le_iff_imp.mp (mono l hs)) ht
