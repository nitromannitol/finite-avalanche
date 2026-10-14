import FiniteAvalanchesCurrent.RegisteredPast.Consumers.Reduction
import CurrentRegisteredPast.MainApplications
import CurrentMean.Supplier
import FiniteAvalanchesCurrent.RegisteredPast.Main


open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CurrentRegisteredPastChecks

theorem entire_integer_main :
    (∀ᵐ η ∂(FullInteger.sourceLaw : Measure (Site2 → ℤ)),
      ∃ w : List Site2, RawFull.Stabilizes η (oneGrain (0 : Site2)) w) ∧
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
      (FullInteger.sourceLaw : Measure (Site2 → ℤ)).real
        {η | ENNReal.ofReal R < extendedCount (FullInteger.radius η (0 : Site2))} ≤
        C * Real.rpow (Real.log (R + 2)) (-a) := by
  exact FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin

/-- The same produced exponent and constant are used at two nonintegral thresholds. -/
theorem same_witness_two_real_thresholds :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ,
      (∀ R ∈ ({(1 / 2 : ℝ), (3 / 2 : ℝ)} : Finset ℝ),
        (FullInteger.sourceLaw : Measure (Site2 → ℤ)).real
          {η | ENNReal.ofReal R < extendedCount (FullInteger.radius η (0 : Site2))} ≤
          C * Real.rpow (Real.log (R + 2)) (-a)) := by
  obtain ⟨a, ha, C, hC⟩ := FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin.2
  refine ⟨a, ha, C, ?_⟩
  intro R hR
  have hn : 0 ≤ R := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl <;> norm_num
  exact hC R hn

/-- Actual stabilization is obtained without a supplied natural-field conclusion. -/
theorem actual_legal_stabilization :
    ∀ᵐ η ∂(FullInteger.sourceLaw : Measure (Site2 → ℤ)),
      ∃ w : List Site2, RawFull.Stabilizes η (oneGrain (0 : Site2)) w :=
  FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin.1

/-- The unchanged produced mean witness includes the true endpoint N=r. -/
theorem actual_mean_endpoint :
    ∃ a C : ℝ, 0 < a ∧ ∀ r : ℕ, ∀ _hr : 2 ≤ r,
      (∫ t, TreeMeasurability11.finiteZN r
        (FiniteAvalanches.Sandpile.SourceCounting.sourceMarks r)
        (Finset.insert_nonempty _ _) t ∂FiniteAvalanches.Sandpile.WiredTrees.law r) ≤
        C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) := by
  obtain ⟨a, C, ha, hB⟩ := FiniteAvalanches.Paper.CurrentMean.uniform_source_reciprocal_bound
  exact ⟨a, C, ha, fun r hr =>
    FiniteAvalanches.Paper.RegisteredPast.Applications.source_bound_endpoint a C hB r hr⟩

end CurrentRegisteredPastChecks
