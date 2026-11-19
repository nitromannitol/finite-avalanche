import FiniteAvalanches.Support.Plane.CrossingBoundaryAccess

/-!
# Separation of crossing stub tails

Distinct crossing stubs, and hence their terminal subpaths, meet only at a
common crossing point.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Distinct sides of disjoint injective crossings meet only at a common midpoint. -/
theorem midpointStub_inter_subset {E X : Type*} [TopologicalSpace X]
    (q : E → unitInterval → X) (hq : ∀ e, Continuous (q e))
    (hinj : ∀ e, Function.Injective (q e))
    (hd : ∀ e f, e ≠ f → Disjoint (range (q e)) (range (q f)))
    {i j : E × Bool} (hij : i ≠ j) :
    range (midpointStub (q i.1) (hq i.1) i.2) ∩
      range (midpointStub (q j.1) (hq j.1) j.2) ⊆
        {q i.1 ⟨1 / 2, by norm_num⟩} ∩ {q j.1 ⟨1 / 2, by norm_num⟩} := by
  rcases i with ⟨e, b⟩
  rcases j with ⟨f, c⟩
  by_cases hef : e = f
  · subst f
    have hbc : b ≠ c := fun h => hij (by cases h; rfl)
    have hmeet := crossingStub_inter_opposite (q e) (hq e) (hinj e)
    cases b <;> cases c <;> simp only [ne_eq, not_true_eq_false] at hbc
    · change range (crossingStub (q e) (hq e) false) ∩
        range (crossingStub (q e) (hq e) true) ⊆ _
      rw [hmeet]
      exact subset_inter (Subset.refl _) (Subset.refl _)
    · change range (crossingStub (q e) (hq e) true) ∩
        range (crossingStub (q e) (hq e) false) ⊆ _
      rw [inter_comm, hmeet]
      exact subset_inter (Subset.refl _) (Subset.refl _)
  · have hdisj : Disjoint (range (midpointStub (q e) (hq e) b))
        (range (midpointStub (q f) (hq f) c)) :=
      crossingStub_disjoint_of_disjoint (q e) (q f) (hq e) (hq f) b c (hd e f hef)
    rw [disjoint_iff_inter_eq_empty] at hdisj
    rw [hdisj]
    exact empty_subset _

/-- Terminal portions of distinct stubs meet only at a common midpoint. -/
theorem midpointStub_subpath_inter_subset {E X : Type*} [TopologicalSpace X]
    (q : E → unitInterval → X) (hq : ∀ e, Continuous (q e))
    (hinj : ∀ e, Function.Injective (q e))
    (hd : ∀ e f, e ≠ f → Disjoint (range (q e)) (range (q f)))
    (u : E × Bool → unitInterval) {i j : E × Bool} (hij : i ≠ j) :
    range ((midpointStub (q i.1) (hq i.1) i.2).subpath (u i) 1) ∩
      range ((midpointStub (q j.1) (hq j.1) j.2).subpath (u j) 1) ⊆
        {q i.1 ⟨1 / 2, by norm_num⟩} ∩ {q j.1 ⟨1 / 2, by norm_num⟩} := by
  apply (inter_subset_inter ?_ ?_).trans (midpointStub_inter_subset q hq hinj hd hij)
  all_goals
    rw [Path.range_subpath]
    exact image_subset_range _ _

end FiniteAvalanches.Electrical.StatementGeometry
