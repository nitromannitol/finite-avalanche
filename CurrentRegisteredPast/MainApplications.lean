import CurrentRegisteredPast.Origin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Paper.RegisteredPast.Applications
open FiniteAvalanches.Paper.CurrentMain
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory Filter
open FiniteAvalanches.External.SandpileLimit
open FiniteAvalanches.Sandpile.SourceCounting TreeMeasurability11
open TreeMeasurability11.CurrentDomain
open scoped Classical ENNReal
noncomputable section

/-- The same current reduction is actually applied at the admissible threshold 2r. -/
theorem radius_two_r_le_finite_reciprocal_limsup :
    ∃ E : ℝ, ∀ r : ℕ, 2 ≤ r →
      (infiniteVolumeLaw : Measure StableField).real
        {η | ENNReal.ofReal ((2 * r : ℕ) : ℝ) < extendedCount (radius η 0)} ≤
        limsup (fun N : ℕ => ∫ t, finiteZN N (sourceMarks r)
          (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) atTop +
        E * (r : ℝ) * (((2 * r : ℕ) : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨E, hE⟩ := RegisteredPast.RadiusReductionFull.reciprocal_reduction_limsup_current
  refine ⟨E, ?_⟩
  intro r hr
  exact hE r hr (2 * r) (by omega)

/-- The uniform source premise includes the first valid volume, N=r. -/
theorem source_bound_endpoint (a C : ℝ)
    (hfinite : ∀ r : ℕ, ∀ hr : 2 ≤ r, ∀ N : ℕ, ∀ hrN : r ≤ N,
      (∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t ∂WiredTrees.law N) ≤
        C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a))
    (r : ℕ) (hr : 2 ≤ r) :
    (∫ t, finiteZN r (sourceMarks r) (Finset.insert_nonempty _ _) t ∂WiredTrees.law r) ≤
      C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) := by
  rw [← source_reciprocal_mean_eq_auxiliary hr le_rfl]
  exact hfinite r hr r le_rfl

/-- Elimination of one shared exponent and constant supplies every argument of the assembly. -/
theorem exact_origin_application_of_source_bound
    (hfinite : ∃ a C : ℝ, 0 < a ∧
      ∀ r : ℕ, ∀ hr : 2 ≤ r, ∀ N : ℕ, ∀ hrN : r ≤ N,
        (∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
          (fun _ hx => sourceMarks_inBox hr hrN hx) t ∂WiredTrees.law N) ≤
          C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a)) :
    (∀ᵐ η ∂(infiniteVolumeLaw : Measure StableField),
      ∃ w : List Site2, Stabilizes η (oneGrain (0 : Site2)) w) ∧
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ,
      ∀ R : ℝ, 0 ≤ R →
        (infiniteVolumeLaw : Measure StableField).real
          {η | ENNReal.ofReal R < extendedCount (radius η (0 : Site2))} ≤
        C * Real.rpow (Real.log (R + 2)) (-a) := by
  obtain ⟨a, C, ha, hB⟩ := hfinite
  exact RegisteredPast.Origin.main_origin_of_source_reciprocal_bound a C ha hB

end
end FiniteAvalanches.Paper.RegisteredPast.Applications

#print axioms FiniteAvalanches.Paper.CurrentMain.source_reciprocal_mean_eq_auxiliary
#print axioms FiniteAvalanches.Paper.CurrentMain.finite_reciprocal_limsup_le_source_bound
#print axioms FiniteAvalanches.Paper.RegisteredPast.Origin.main_origin_of_source_reciprocal_bound
#print axioms FiniteAvalanches.Paper.RegisteredPast.Applications.radius_two_r_le_finite_reciprocal_limsup
#print axioms FiniteAvalanches.Paper.RegisteredPast.Applications.source_bound_endpoint
#print axioms FiniteAvalanches.Paper.RegisteredPast.Applications.exact_origin_application_of_source_bound
