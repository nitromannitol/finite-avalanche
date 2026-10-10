import FiniteAvalanches.Trees.Lattice.ReciprocalFiniteDetermination
import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false
open LatticeProb MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
namespace ReciprocalLimit15
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice TreeMeasurability11

/-- The actual finite reciprocal is bounded, including the zero sink-ancestor and
outside-volume branches, with the full original-copy denominator. -/
theorem finiteZN_bounds (N : ℕ) (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : (WiredTrees.graph N).SpanningTree) :
    0 ≤ finiteZN N S hS t ∧ finiteZN N S hS t ≤ 1 := by
  unfold finiteZN
  split
  · exact (WiredTrees.graph N).reciprocalWeight_one_nonneg_le_one none (finiteMarks N S)
      (finiteMarks_nonempty N S hS ‹∀ x ∈ S, FiniteWired.inBox N x›) t
  · exact ⟨le_rfl, zero_le_one⟩

/-- The actual finite-wired reciprocal expectation converges for every finite
nonempty source set. No local determination or convergence premise is supplied. -/
theorem actual_reciprocal_expectation_limit (S : Finset (Site 2)) (hS : S.Nonempty) :
    Tendsto (fun N : ℕ => ∫ t, finiteZN N S hS t ∂WiredTrees.law N) atTop
      (nhds (∫ T, infiniteReciprocal S hS T ∂endedUST)) := by
  have hFinMeas (N : ℕ) : Measurable (finiteZN N S hS) := measurable_of_countable _
  let νN : ℕ → ProbabilityMeasure ℝ := fun N =>
    ⟨(WiredTrees.law N).map (finiteZN N S hS),
      Measure.isProbabilityMeasure_map (hFinMeas N).aemeasurable⟩
  let ν : ProbabilityMeasure ℝ :=
    ⟨endedUST.map (infiniteReciprocal S hS),
      Measure.isProbabilityMeasure_map (measurable_infiniteReciprocal S hS).aemeasurable⟩
  have hweak : Tendsto νN atTop (nhds ν) := by
    apply tendsto_of_forall_isOpen_le_liminf_nat'
    intro U hU
    -- These open unions consist of literal cylinders on which finite values
    -- enter U at every sufficiently large volume. All witnesses are proved below.
    let G : ℕ → Set EdgeField := fun R =>
      ⋃ F : Finset LatticeEdge, ⋃ p : F → Bool,
        ⋃ (_hFin : ∀ N ≥ R, ∀ t : (WiredTrees.graph N).SpanningTree,
          wiredField t ∈ cylinder F p → finiteZN N S hS t ∈ U), cylinder F p
    have hOpen (R : ℕ) : IsOpen (G R) :=
      isOpen_iUnion fun F => isOpen_iUnion fun p =>
        isOpen_iUnion fun _ => (isClopen_cylinder F p).isOpen
    have hmono : Monotone G := by
      intro R Q hRQ ω hω
      simp only [G, Set.mem_iUnion] at hω ⊢
      obtain ⟨F,p,hFin,hw⟩ := hω
      exact ⟨F,p,fun N hN t ht => hFin N (hRQ.trans hN) t ht,hw⟩
    have hfinite (R N : ℕ) (hN : R ≤ N) (t : (WiredTrees.graph N).SpanningTree)
        (ht : wiredField t ∈ G R) : finiteZN N S hS t ∈ U := by
      simp only [G, Set.mem_iUnion] at ht
      obtain ⟨F,p,hFin,hw⟩ := ht
      exact hFin N hN t hw
    have hcover : (infiniteReciprocal S hS) ⁻¹' U ⊆
        (Subtype.val : EndedTree → EdgeField) ⁻¹' (⋃ R, G R) := by
      intro T hT
      obtain ⟨F,R,hFR⟩ := ReciprocalCertificate14.reciprocal_finite_certificate T S hS
      let p : F → Bool := F.restrict T.val
      have hFin : ∀ N ≥ R, ∀ t : (WiredTrees.graph N).SpanningTree,
          wiredField t ∈ cylinder F p → finiteZN N S hS t ∈ U := by
        intro N hN t hp
        obtain ⟨_,_,_,_,_,_,_,_,_,hZ⟩ := hFR N hN t (fun f hf => congrFun hp ⟨f,hf⟩)
        rw [hZ]
        exact hT
      apply Set.mem_iUnion.mpr
      refine ⟨R,?_⟩
      simp only [G, Set.mem_iUnion]
      exact ⟨F,p,hFin,rfl⟩
    have hmass : (ν : Measure ℝ) U ≤
        ⨆ R, (squareLatticeUST : Measure EdgeField) (G R) := by
      change endedUST.map (infiniteReciprocal S hS) U ≤ _
      rw [Measure.map_apply (measurable_infiniteReciprocal S hS) hU.measurableSet,
        ← hmono.measure_iUnion]
      rw [← endedUST_map,
        Measure.map_apply measurable_subtype_coe (isOpen_iUnion hOpen).measurableSet]
      exact measure_mono hcover
    apply hmass.trans
    apply iSup_le
    intro R
    apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      squareLatticeUST_tendsto (hOpen R)).trans
    refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop R] with N hN
    change finiteLaw N (G R) ≤ (WiredTrees.law N).map (finiteZN N S hS) U
    rw [finiteLaw_apply N _ (hOpen R).measurableSet,
      Measure.map_apply (hFinMeas N) hU.measurableSet]
    exact measure_mono (fun t ht => hfinite R N hN t ht)
  let clip : ℝ → ℝ := fun x => max 0 (min 1 x)
  have hclip (x : ℝ) : 0 ≤ clip x ∧ clip x ≤ 1 :=
    ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
  let test : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨clip, continuous_const.max (continuous_const.min continuous_id)⟩ 1 (by
      intro x y
      change dist (clip x) (clip y) ≤ 1
      rw [Real.dist_eq, abs_le]
      have hx := hclip x
      have hy := hclip y
      constructor <;> linarith)
  have htest (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : test x = x := by
    change max 0 (min 1 x) = x
    rw [min_eq_right hx.2,max_eq_right hx.1]
  have hN (N : ℕ) : (∫ x, test x ∂(νN N : Measure ℝ)) =
      ∫ t, finiteZN N S hS t ∂WiredTrees.law N := by
    change (∫ x, test x ∂(WiredTrees.law N).map (finiteZN N S hS)) = _
    rw [integral_map (hFinMeas N).aemeasurable test.continuous.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun t => htest _ (finiteZN_bounds N S hS t))
  have hInf : (∫ x, test x ∂(ν : Measure ℝ)) = ∫ T, infiniteReciprocal S hS T ∂endedUST := by
    change (∫ x, test x ∂endedUST.map (infiniteReciprocal S hS)) = _
    rw [integral_map (measurable_infiniteReciprocal S hS).aemeasurable
      test.continuous.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun T => htest _ (infiniteReciprocal_bounds S hS T))
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) test
  simpa only [hN,hInf] using h

#print axioms finiteZN_bounds
#print axioms actual_reciprocal_expectation_limit
end ReciprocalLimit15
