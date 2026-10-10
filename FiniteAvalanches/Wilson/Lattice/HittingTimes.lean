import FiniteAvalanches.Wilson.Lattice.SimpleWalk

/-! Literal first hitting times with top for a genuinely infinite avoiding path.
Their comparison agrees with the ordered source event, including time zero. -/
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb
open scoped Classical
noncomputable section

def firstHit (U : Set (Site 2)) (p : ℕ → Site 2) : WithTop ℕ :=
  if h : ∃ n, p n ∈ U then (Nat.find h : WithTop ℕ) else ⊤

theorem firstHit_eq_top_iff (U : Set (Site 2)) (p : ℕ → Site 2) :
    firstHit U p = ⊤ ↔ ∀ n, p n ∉ U := by
  by_cases h : ∃ n, p n ∈ U
  · simp [firstHit, h]
  · have hn : ∀ n, p n ∉ U := fun n hm => h ⟨n, hm⟩
    simp only [firstHit, dif_neg h, eq_self, true_iff]
    exact hn

theorem firstHit_eq_zero_iff (U : Set (Site 2)) (p : ℕ → Site 2) :
    firstHit U p = 0 ↔ p 0 ∈ U := by
  by_cases h : ∃ n, p n ∈ U
  · rw [firstHit, dif_pos h]
    exact_mod_cast (Nat.find_eq_zero h)
  · simp only [firstHit, dif_neg h, WithTop.top_ne_zero, false_iff]
    exact fun hp => h ⟨0, hp⟩

theorem hitBefore_iff_firstHit_lt (A C : Set (Site 2)) (x : Site 2) (d : WalkDriver) :
    d ∈ hitBefore A C x ↔ firstHit C (position x d) < firstHit A (position x d) := by
  constructor
  · rintro ⟨n, hnC, hnA⟩
    have hC : ∃ m, position x d m ∈ C := ⟨n, hnC⟩
    by_cases hA : ∃ m, position x d m ∈ A
    · have hna : n < Nat.find hA := by
        by_contra h
        exact hnA (Nat.find hA) (Nat.le_of_not_gt h) (Nat.find_spec hA)
      have hl := Nat.lt_of_le_of_lt (Nat.find_min' hC hnC) hna
      simp only [firstHit, dif_pos hC, dif_pos hA]
      exact_mod_cast hl
    · simp [firstHit, hC, hA]
  · intro h
    have hC : ∃ m, position x d m ∈ C := by
      by_contra hC
      simp only [firstHit, dif_neg hC, not_top_lt] at h
    refine ⟨Nat.find hC, Nat.find_spec hC, ?_⟩
    intro m hm hmA
    have hA : ∃ n, position x d n ∈ A := ⟨m, hmA⟩
    have hl : Nat.find hC < Nat.find hA := by
      simp only [firstHit, dif_pos hC, dif_pos hA] at h
      exact_mod_cast h
    have ha := Nat.find_min' hA hmA
    omega

end
end FiniteAvalanches.Wilson.Lattice
