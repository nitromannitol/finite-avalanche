import FiniteAvalanches.Sandpile.SourceCounting.ObservedCofiniteGeometry
import FiniteAvalanches.Sandpile.SourceCounting.ConditionalAveraging

/-! The cofinite forest estimate on every actual finite observation cell. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open TreeMeasurability11
open scoped Classical
noncomputable section

/-- One universal exponent and constant bound the integrable conditional
reciprocal on every actual nonsink observation, using the entire forest estimate. -/
theorem source_marks_conditional_bound_of_cofinite_reciprocal
    (hforest :
    ∃ a C : ℝ, 0 < a ∧ ∀ K : Finset (Site 2),
        ((lattice 2).induce (K : Set (Site 2))).Connected →
        ∀ γ : Set (Site 2), ((lattice 2).induce γ).Connected →
          γᶜ.Finite → Disjoint (K : Set (Site 2)) γ →
          (∃ k ∈ K, ∃ y ∈ γ, (lattice 2).Adj k y) →
          ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
            (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
              C * Real.rpow
                (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
                (-a)) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ r : ℕ, 2 ≤ r → ∀ N : ℕ, r ≤ N →
      ∀ t₀ : (graph N).SpanningTree,
        (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
          (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none →
        Integrable (finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _))
          (ProbabilityTheory.cond (law N) {t | (graph N).copiedConnectorObservation t₀ t none
            (markedVertices (activeMarks N r))
            (marked_vertices_nonempty _ (source_mem_activeMarks N r))}) ∧
        (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t
          ∂ProbabilityTheory.cond (law N) {t | (graph N).copiedConnectorObservation t₀ t none
            (markedVertices (activeMarks N r))
            (marked_vertices_nonempty _ (source_mem_activeMarks N r))}) ≤
          C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) := by
  obtain ⟨a, C, ha, hbound⟩ := hforest
  have hC : 0 < max C 1 := lt_of_lt_of_le (by norm_num) (le_max_right C 1)
  refine ⟨a, max C 1, ha, hC, ?_⟩
  intro r hr N hrN t₀ hne
  refine ⟨source_marks_conditional_finiteZN_integrable hr hrN t₀, ?_⟩
  rw [source_marks_conditional_finiteZN_expectation hr hrN t₀ hne]
  obtain ⟨hK, hΓ, hfin, hdisj, hadj, hzero, hdiam⟩ :=
    source_marks_observed_cofinite_geometry hr hrN t₀ hne
  let K := activeSites N ((graph N).span t₀ (markedVertices (activeMarks N r)))
  let Q := observationRootPair N (markedVertices (activeMarks N r))
    (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t₀ hne
  have hf := hbound K hK Q.one hΓ hfin hdisj hadj Q hzero rfl
  have hlog : 0 < Real.log ((r : ℝ) + 2) := Real.log_pos (by
    have := Nat.cast_nonneg (α := ℝ) r
    linarith)
  have hlogle : Real.log ((r : ℝ) + 2) ≤
      Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2) := by
    apply Real.log_le_log (by positivity)
    have hd : (r : ℝ) ≤ ((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) := by
      exact_mod_cast hdiam
    linarith only [hd]
  have hpow := Real.rpow_le_rpow_of_nonpos hlog hlogle (neg_nonpos.mpr ha.le)
  have hnn := Real.rpow_nonneg (Real.log_nonneg (show (1 : ℝ) ≤
    ((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2 by
      have := Nat.cast_nonneg (α := ℝ) (K.sup (fun x => K.sup (fun y => siteRadius x y)))
      linarith)) (-a)
  exact hf.trans ((mul_le_mul_of_nonneg_right (le_max_left C 1) hnn).trans
    (mul_le_mul_of_nonneg_left hpow hC.le))

/-- Real finite partition averaging includes every sink cell with its exact
zero reciprocal and retains the whole copied spanning-tree probability law. -/
theorem source_marks_uniform_finiteZN_bound_of_cofinite_reciprocal
    (hforest :
    ∃ a C : ℝ, 0 < a ∧ ∀ K : Finset (Site 2),
        ((lattice 2).induce (K : Set (Site 2))).Connected →
        ∀ γ : Set (Site 2), ((lattice 2).induce γ).Connected →
          γᶜ.Finite → Disjoint (K : Set (Site 2)) γ →
          (∃ k ∈ K, ∃ y ∈ γ, (lattice 2).Adj k y) →
          ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
            (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
              C * Real.rpow
                (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
                (-a)) :
    ∃ a C : ℝ, 0 < a ∧ ∀ r : ℕ, 2 ≤ r → ∀ N : ℕ, r ≤ N →
      (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂law N) ≤
        C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) := by
  obtain ⟨a, C, ha, hC, hbound⟩ :=
    source_marks_conditional_bound_of_cofinite_reciprocal hforest
  refine ⟨a, C, ha, ?_⟩
  intro r hr N hrN
  have hlog : 0 < Real.log ((r : ℝ) + 2) := Real.log_pos (by
    have := Nat.cast_nonneg (α := ℝ) r
    linarith)
  apply source_marks_finiteZN_integral_le_of_conditional_bound hr hrN _
    (mul_nonneg hC.le (Real.rpow_nonneg hlog.le (-a)))
  intro t₀ hne
  exact (hbound r hr N hrN t₀ hne).2

end
end FiniteAvalanches.ConditioningConsumer
