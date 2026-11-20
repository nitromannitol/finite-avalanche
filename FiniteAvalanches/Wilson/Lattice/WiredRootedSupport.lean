import FiniteAvalanches.Wilson.Lattice.SamplerRootExhaustion

/-! The recurrent Wilson cylinder law is supported on rooted forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical ENNReal

noncomputable section

/-- Every fixed site reaches an original root almost surely under the cylinder law. -/
theorem IsWilsonCylinderLaw.ae_reaches_root (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν) (x : Site 2) :
    ∀ᵐ ω ∂(ν : Measure ForestField), ∃ r ∈ R.zero ∪ R.one,
      (toGraph ω.1).Reachable x r := by
  let A : ℕ → Set (ℕ → WalkDriver) := fun n =>
    samplerEdgeObservation R
      ((List.range (rootEdgeQueryLength x (finiteEdgeExhaustion n))).map
        (rootEdgeQueries x (finiteEdgeExhaustion n))) (finiteEdgeExhaustion n) ⁻¹'
      rootConnectionPattern R x (finiteEdgeExhaustion n)
  have hA : ∀ n, MeasurableSet (A n) := by
    intro n
    exact ((Set.to_countable (rootConnectionPattern R x (finiteEdgeExhaustion n))).measurableSet).preimage
      (measurable_samplerEdgeObservation R _ _)
  have hpoint : ∀ᵐ rows ∂wilsonRows, ∀ᶠ n : ℕ in atTop,
      rows ∈ A n ↔ rows ∈ (Set.univ : Set (ℕ → WalkDriver)) := by
    filter_upwards [wilsonRows_ae_eventually_rootConnectionPattern R x] with rows hrows
    filter_upwards [hrows] with n hn
    simp only [Set.mem_univ, iff_true]
    exact hn
  have ht : Tendsto (fun n => wilsonRows (A n)) atTop (nhds 1) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      (μ := wilsonRows) (A := Set.univ) (As := A) MeasurableSet.univ hA hpoint
    simpa only [measure_univ] using h
  have hb : ∀ n, wilsonRows (A n) ≤ (ν : Measure ForestField) (rootConnectionEvent R x) := by
    intro n
    let E := finiteEdgeExhaustion n
    let q := rootEdgeQueries x E
    let m := rootEdgeQueryLength x E
    have hq := rootEdgeQueries_spec x E
    have hm := hν.rootConnectionPattern_measure R ν x q m E hq.2.2
    change wilsonRows (samplerEdgeObservation R ((List.range m).map q) E ⁻¹'
      rootConnectionPattern R x E) ≤ _
    rw [← hm]
    exact measure_mono (restrictEdgeField_rootConnection_subset R x E)
  have hlower : 1 ≤ (ν : Measure ForestField) (rootConnectionEvent R x) :=
    le_of_tendsto ht (Eventually.of_forall hb)
  have hupper : (ν : Measure ForestField) (rootConnectionEvent R x) ≤ 1 := by
    simpa only [measure_univ] using
      (measure_mono (μ := (ν : Measure ForestField)) (Set.subset_univ (rootConnectionEvent R x)))
  have hone : (ν : Measure ForestField) (rootConnectionEvent R x) = 1 :=
    le_antisymm hupper hlower
  exact (mem_ae_iff_prob_eq_one (isOpen_rootConnectionEvent R x).measurableSet).mpr hone

/-- The cylinder law is almost surely supported on forests with exactly one
original root in every component. -/
theorem IsWilsonCylinderLaw.ae_rooted (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν) :
    ∀ᵐ ω ∂(ν : Measure ForestField), is_rooted_forest R ω.1 := by
  have hroots : ∀ᵐ ω ∂(ν : Measure ForestField), ∀ x : Site 2,
      ∃ r ∈ R.zero ∪ R.one, (toGraph ω.1).Reachable x r := by
    apply ae_all_iff.mpr
    exact hν.ae_reaches_root R ν
  filter_upwards [hν.ae_acyclic R ν, hν.ae_roots_separated R ν, hroots] with ω hac hsep hex
  refine ⟨hac, ?_⟩
  intro x
  obtain ⟨r, hr, hxr⟩ := hex x
  refine ⟨r, hr, hxr, ?_⟩
  intro r' hr' hxr'
  exact hsep r' r hr' hr (hxr'.symm.trans hxr)

end
end FiniteAvalanches.Wilson.Lattice
