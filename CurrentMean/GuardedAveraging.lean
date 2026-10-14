import FiniteAvalanches.Paper.Current.ConditionalNaturalMean
import FiniteAvalanches.Sandpile.SourceCounting.ConditionalAveraging

/-! Averaging the guarded source reciprocal over complete copied observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Paper.CurrentMean
open Function
open LatticeProb MeasureTheory FiniteAvalanches FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.ConditioningConsumer TreeMeasurability11.CurrentDomain
open scoped Classical ENNReal
noncomputable section

/-- Every guarded source reciprocal is integrable from its genuine finite bounds. -/
theorem integrable_source_reciprocal {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    Integrable (sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
      (fun _ hx => sourceMarks_inBox hr hrN hx)) (law N) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_of_countable _).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun t => ?_
  have hb := sourceFiniteReciprocal_bounds N (sourceMarks r) (Finset.insert_nonempty _ _)
    (fun _ hx => sourceMarks_inBox hr hrN hx) t
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

/-- The same finite bounds give integrability on each actual positive complete observation. -/
theorem integrable_source_reciprocal_conditional {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree) :
    Integrable (sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
      (fun _ hx => sourceMarks_inBox hr hrN hx))
      (ProbabilityTheory.cond (law N)
        {t | (graph N).copiedConnectorObservation t₀ t none
          (markedVertices (activeMarks N r))
          (marked_vertices_nonempty _ (source_mem_activeMarks N r))}) := by
  haveI := ProbabilityTheory.cond_isProbabilityMeasure
    (finite_whole_observation_pos N (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t₀).ne'
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_of_countable _).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun t => ?_
  have hb := sourceFiniteReciprocal_bounds N (sourceMarks r) (Finset.insert_nonempty _ _)
    (fun _ hx => sourceMarks_inBox hr hrN hx) t
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

/-- Finite quotient averaging includes zero-measure fibers rather than dividing by them. -/
theorem integral_le_of_complete_partition {X : Type*} [Finite X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
    [IsProbabilityMeasure μ] (s : Setoid X) (f : X → ℝ) (hf : Integrable f μ)
    (B : ℝ)
    (hbound : ∀ x, μ {y | s.r x y} ≠ 0 →
      (∫ y, f y ∂ProbabilityTheory.cond μ {y | s.r x y}) ≤ B) :
    (∫ x, f x ∂μ) ≤ B := by
  letI : Fintype (Quotient s) := Fintype.ofFinite _
  let P (q : Quotient s) : Set X := {x | s.r q.out x}
  have hmeas (q : Quotient s) : MeasurableSet (P q) := (Set.toFinite _).measurableSet
  have hcover : (⋃ q, P q) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨Quotient.mk s x,Quotient.mk_out x⟩
  have hdisjoint : Pairwise (Disjoint on P) := by
    intro q q' hne
    apply Set.disjoint_left.mpr
    intro x hx hx'
    have he : Quotient.mk s q.out = Quotient.mk s q'.out :=
      Quotient.sound (s.trans hx (s.symm hx'))
    rw [Quotient.out_eq,Quotient.out_eq] at he
    exact hne he
  have hcell (q : Quotient s) : (∫ x in P q, f x ∂μ) ≤ ∫ _ in P q, B ∂μ := by
    by_cases hm0 : μ (P q) = 0
    · rw [Measure.restrict_eq_zero.mpr hm0,integral_zero_measure,integral_zero_measure]
    · have hmR : (μ (P q)).toReal ≠ 0 :=
        ne_of_gt (ENNReal.toReal_pos hm0 (measure_ne_top _ _))
      have hc := hbound q.out hm0
      change (∫ y, f y ∂ProbabilityTheory.cond μ (P q)) ≤ B at hc
      rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul] at hc
      have hmul := mul_le_mul_of_nonneg_left hc (ENNReal.toReal_nonneg :
        0 ≤ (μ (P q)).toReal)
      rw [← mul_assoc,mul_inv_cancel₀ hmR,one_mul] at hmul
      simpa only [setIntegral_const,smul_eq_mul,measureReal_def] using hmul
  calc
    (∫ x, f x ∂μ) = ∑ q, ∫ x in P q, f x ∂μ := by
      rw [← integral_iUnion_fintype hmeas hdisjoint (fun _ => hf.integrableOn),
        hcover,Measure.restrict_univ]
    _ ≤ ∑ q, ∫ _ in P q, B ∂μ := Finset.sum_le_sum (fun q _ => hcell q)
    _ = ∫ _ : X, B ∂μ := by
      rw [← integral_iUnion_fintype hmeas hdisjoint
        (fun _ => (integrable_const B).integrableOn),hcover,Measure.restrict_univ]
    _ = B := by rw [integral_const,probReal_univ,one_smul]

                                                                             
                                                                             
theorem source_mean_le_of_forest (a C : ℝ) (ha : 0 < a)
    (hforest : ∀ K : Finset (Site 2), ((lattice 2).induce (K : Set (Site 2))).Connected →
      ∀ γ : Set (Site 2), ((lattice 2).induce γ).Connected → γᶜ.Finite →
        Disjoint (K : Set (Site 2)) γ →
        (∃ k ∈ K, ∃ y ∈ γ, (lattice 2).Adj k y) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
        (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
          C * Real.rpow (Real.log
            (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2)) (-a))
    (r : ℕ) (hr : 2 ≤ r) (N : ℕ) (hrN : r ≤ N) :
    (∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
      (fun _ hx => sourceMarks_inBox hr hrN hx) t ∂law N) ≤
        max C 0 * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) := by
  let S := markedVertices (activeMarks N r)
  let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
  let f := sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
    (fun _ hx => sourceMarks_inBox hr hrN hx)
  let obs : Setoid (graph N).SpanningTree :=
    ⟨fun t₀ t => (graph N).copiedConnectorObservation t₀ t none S hS,
      copiedConnectorObservation_equivalence (graph N) none S hS⟩
  have hlog : 0 < Real.log ((r : ℝ) + 2) := Real.log_pos (by
    have := Nat.cast_nonneg (α := ℝ) r
    linarith)
  have hB : 0 ≤ max C 0 * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) :=
    mul_nonneg (le_max_right C 0) (Real.rpow_nonneg hlog.le _)
  apply integral_le_of_complete_partition (law N) obs f
    (integrable_source_reciprocal hr hrN)
  intro t₀ _hpopulated
  have _hpositive : 0 < law N {t | obs.r t₀ t} := finite_whole_observation_pos N S hS t₀
  have _hInt := integrable_source_reciprocal_conditional hr hrN t₀
  by_cases hne : (graph N).ancestorOf t₀ none S hS ≠ none
  · let K := activeSites N ((graph N).span t₀ S)
    let R := observationRootPair N S hS t₀ hne
    obtain ⟨_hpos,hK,hΓ,hfin,hd,hadj,hzero,hdiam,_hmean⟩ :=
      CountDictionaryReview.actual_mean_main_inputs hr hrN t₀ hne
    have hnatural := CountDictionaryReview.actual_guarded_conditional_natural_mean hr hrN t₀ hne
    dsimp only at hnatural hdiam hzero
    change (∫ t, f t ∂ProbabilityTheory.cond (law N) {t | obs.r t₀ t}) =
      ∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R at hnatural
    rw [hnatural]
    have hF := hforest K hK R.one hΓ hfin hd hadj R hzero rfl
    have hdr : (r : ℝ) ≤ ((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hdiam
    have hlogle : Real.log ((r : ℝ) + 2) ≤
        Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith only [hdr])
    have hanti := Real.rpow_le_rpow_of_nonpos hlog hlogle (neg_nonpos.mpr ha.le)
    calc
      _ ≤ C * Real.rpow (Real.log
          (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2)) (-a) := hF
      _ ≤ max C 0 * Real.rpow (Real.log
          (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2)) (-a) :=
        mul_le_mul_of_nonneg_right (le_max_left C 0)
          (Real.rpow_nonneg (hlog.le.trans hlogle) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hanti (le_max_right C 0)
  · have hsink : (graph N).ancestorOf t₀ none S hS = none := not_ne_iff.mp hne
    have hz : (∫ t, f t ∂ProbabilityTheory.cond (law N) {t | obs.r t₀ t}) = 0 := by
      calc
        _ = ∫ _ : (graph N).SpanningTree, (0 : ℝ)
            ∂ProbabilityTheory.cond (law N) {t | obs.r t₀ t} := by
          apply integral_congr_ae
          filter_upwards [ProbabilityTheory.ae_cond_mem (μ := law N)
            (s := {t | obs.r t₀ t}) (Set.toFinite _).measurableSet] with t ht
          have hs : (graph N).ancestorOf t none S hS = none := ht.2.2.1.trans hsink
          change sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
            (fun _ hx => sourceMarks_inBox hr hrN hx) t = 0
          rw [sourceFiniteReciprocal,← CountDictionaryReview.source_marks_extended_eq_guarded hr hrN t,
            FiniteAvalanches.Paper.CurrentDF176.finiteExtendedContacts_of_sink N S hS t hs]
          simp only [ENNReal.inv_top,ENNReal.toReal_zero]
        _ = 0 := integral_zero _ _
    exact hz ▸ hB

end
end FiniteAvalanches.Paper.CurrentMean
