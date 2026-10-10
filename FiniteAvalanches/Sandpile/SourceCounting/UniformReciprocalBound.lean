import FiniteAvalanches.Wilson.Lattice.ForestRootApplication
import FiniteAvalanches.Sandpile.SourceCounting.ObservedExitRay
import FiniteAvalanches.Sandpile.SourceCounting.ConditionalAveraging

/-! An ordinary conditional uniform bound for the actual finite source reciprocal. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open TreeMeasurability11
open scoped Classical
noncomputable section

/-- The exact closed forest estimate implies a uniform actual finite-volume
reciprocal expectation bound. The forest estimate remains an explicit input. -/
theorem source_marks_uniform_finiteZN_bound_of_closed_forest_bound
    (hforest : ∃ a C : ℝ, 0 < a ∧ ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      ∀ γ : SimpleRay, Disjoint (K : Set (Site 2)) γ.vertices →
        (∃ k ∈ K, (lattice 2).Adj k (γ.vertex 0)) →
        ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ.vertices →
          (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
            C * Real.rpow
              (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
              (-a)) :
    ∃ a C : ℝ, 0 < a ∧ ∀ r : ℕ, 2 ≤ r → ∀ N : ℕ, r ≤ N →
      (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂law N) ≤
        C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) := by
  obtain ⟨a, C, ha, hC, hbound⟩ :=
    ConditionalInternal.uniform_enlarged_roots_bound_of_closed_forest_bound hforest
  refine ⟨a, C, ha, ?_⟩
  intro r hr N hrN
  have hlog : 0 < Real.log ((r : ℝ) + 2) := by
    apply Real.log_pos
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith only [hr0]
  have hB : 0 ≤ C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) :=
    mul_nonneg hC.le (Real.rpow_nonneg hlog.le (-a))
  apply source_marks_finiteZN_integral_le_of_conditional_bound hr hrN _ hB
  intro t hne
  rw [source_marks_conditional_finiteZN_expectation hr hrN t hne]
  obtain ⟨_, hconnected, _, _, _, hdiam, hroots, ancestor, γ,
    _, hancestor, hadj, hΓ, hdisj, _⟩ :=
    source_marks_observation_escaping_ray hr hrN t hne
  exact hbound r _ hconnected hdiam γ hdisj
    ⟨FiniteWired.site ancestor, hancestor, hadj⟩ _ hroots hΓ

end
end FiniteAvalanches.ConditioningConsumer
