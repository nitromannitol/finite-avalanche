import FiniteAvalanches.Wilson.Lattice.ColorMarginal

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb MeasureTheory
open scoped Classical ENNReal
noncomputable section

private theorem measurable_color_one (x : Site 2) :
    MeasurableSet {σ : ColorField | σ x = true} :=
  (isClosed_eq (continuous_apply x : Continuous (fun σ : ColorField => σ x))
    continuous_const).measurableSet

private theorem measurable_color_indicator (x : Site 2) :
    Measurable (fun σ : ColorField => if σ x = true then (1 : ℝ≥0∞) else 0) :=
  Measurable.ite (measurable_color_one x) measurable_const measurable_const

/-- The expectation counts every original nearest-neighbor contact, one summand per edge. -/
theorem contact_expectation_eq_hitting (R : RootPair) (F : Finset (Site 2)) :
    (∫⁻ σ, ∑ x ∈ F, ∑ y ∈ nbrFinset x,
      if σ y = true then (1 : ℝ≥0∞) else 0 ∂wilsonColorLaw R) =
      ∑ x ∈ F, ∑ y ∈ nbrFinset x, walkLaw (hitBefore R.zero R.one y) := by
  rw [lintegral_finsetSum F (fun x _ =>
    Finset.measurable_sum (nbrFinset x) (fun y _ => measurable_color_indicator y))]
  apply Finset.sum_congr rfl
  intro x hx
  rw [lintegral_finsetSum (nbrFinset x) (fun y _ => measurable_color_indicator y)]
  apply Finset.sum_congr rfl
  intro y hy
  calc
    (∫⁻ σ, if σ y = true then (1 : ℝ≥0∞) else 0 ∂wilsonColorLaw R) =
        wilsonColorLaw R {σ | σ y = true} := by
      simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
        (lintegral_indicator_one (μ := wilsonColorLaw R) (measurable_color_one y))
    _ = walkLaw (hitBefore R.zero R.one y) := wilsonColorLaw_single_vertex R y

/-- The actual added-root loss is controlled by the genuine first-exit hitting sum. -/
theorem added_contacts_expectation_le_firstExit (R : RootPair)
    (K Z : Finset (Site 2)) (N : ℕ) (hZ : (↑Z : Set (Site 2)) ⊆ R.zero)
    (hC : R.one ⊆ (↑(box 2 N) : Set (Site 2))ᶜ) :
    (∫⁻ σ, ∑ x ∈ Z \ K, ∑ y ∈ nbrFinset x,
      if σ y = true then (1 : ℝ≥0∞) else 0 ∂wilsonColorLaw R) ≤
      ∑ x ∈ Z, ∑ y ∈ nbrFinset x, walkLaw
        {w | firstHit (↑(box 2 N) : Set (Site 2))ᶜ (position y w) <
          firstHit (↑Z : Set (Site 2)) (position y w)} := by
  rw [contact_expectation_eq_hitting]
  calc
    (∑ x ∈ Z \ K, ∑ y ∈ nbrFinset x, walkLaw (hitBefore R.zero R.one y)) ≤
        ∑ x ∈ Z \ K, ∑ y ∈ nbrFinset x, walkLaw
          {w | firstHit (↑(box 2 N) : Set (Site 2))ᶜ (position y w) <
            firstHit (↑Z : Set (Site 2)) (position y w)} := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      rw [← wilsonColorLaw_single_vertex]
      exact wilsonColorLaw_single_vertex_le_firstExit R Z N hZ hC y
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun _ _ _ => bot_le)

end
end FiniteAvalanches.Wilson.Lattice
#print axioms FiniteAvalanches.Wilson.Lattice.contact_expectation_eq_hitting
#print axioms FiniteAvalanches.Wilson.Lattice.added_contacts_expectation_le_firstExit
