import FiniteAvalanches.Trees.Lattice.InfiniteLaw
import FiniteAvalanches.External.WiredUstOneEnd
import FiniteAvalanches.External.WiredUstDualLaw

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb MeasureTheory FiniteAvalanches.External FiniteAvalanches.Sandpile
open scoped Classical ENNReal
noncomputable section

theorem oneEnded_of_unique_infinite_components (ω : EdgeField) (hT : IsTree ω)
    (hK : ∀ K : Finset (Site 2), ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)),
      (SimpleGraph.ComponentCompl.supp C).Infinite) : OneEnded ω := by
  have hT' : (toGraph ω).IsTree := hT
  haveI : Fact (toGraph ω).Preconnected := ⟨hT'.connected.preconnected⟩
  haveI : Infinite (Site 2) := inferInstance
  refine ⟨Set.nonempty_coe_sort.mpr (SimpleGraph.nonempty_ends_of_infinite (toGraph ω)),
    ⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  funext K
  exact (hK K.unop).unique (SimpleGraph.end_componentCompl_infinite _ a K)
    (SimpleGraph.end_componentCompl_infinite _ b K)

theorem squareLatticeUST_ae_tree_oneEnded :
    ∀ᵐ ω ∂(squareLatticeUST : Measure EdgeField), IsTree ω ∧ OneEnded ω := by
  filter_upwards [square_lattice_wired_ust_one_tree_one_end squareLatticeUST
    squareLatticeUST_tendsto] with ω hω
  exact ⟨hω.1, oneEnded_of_unique_infinite_components ω hω.1 hω.2⟩

theorem squareLatticeUST_cylinder_tendsto (F : Finset LatticeEdge) (p : F → Bool) :
    Filter.Tendsto (fun N : ℕ => (finiteProbability N : Measure EdgeField) (cylinder F p))
      Filter.atTop (nhds ((squareLatticeUST : Measure EdgeField) (cylinder F p))) := by
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    squareLatticeUST_tendsto (E := cylinder F p)
    (by rw [(isClopen_cylinder F p).frontier_eq]; exact measure_empty)

/-- Cylinder probabilities are limits of original copied-tree counts over `treeCount N`. -/
theorem squareLatticeUST_cylinder_count_limit (F : Finset LatticeEdge) (p : F → Bool) :
    Filter.Tendsto
      (fun N : ℕ => (Nat.card ({t : (WiredTrees.graph N).SpanningTree |
          F.restrict (wiredField t) = p} : Set (WiredTrees.graph N).SpanningTree) : ℝ≥0∞) /
        WiredTrees.treeCount N)
      Filter.atTop (nhds ((squareLatticeUST : Measure EdgeField) (cylinder F p))) := by
  apply Filter.Tendsto.congr _ (squareLatticeUST_cylinder_tendsto F p)
  intro N
  change finiteLaw N (cylinder F p) = _
  exact finiteLaw_original_count N (cylinder F p) (measurableSet_cylinder F p)

theorem squareLatticeUST_dual_law :
    (squareLatticeUST : Measure EdgeField).map dualField = (squareLatticeUST : Measure EdgeField) :=
  square_lattice_ust_dual_law squareLatticeUST squareLatticeUST_tendsto

/-- `P[e ∈ T] = P[e† ∉ T]` in the face-lattice naming of dual edges. -/
theorem squareLatticeUST_edge_dual (p : Site 2 × Fin 2) :
    (squareLatticeUST : Measure EdgeField) {ω | ω (baseEdge p) = true} =
      (squareLatticeUST : Measure EdgeField)
        {ω | ω (baseEdge (p.1 + unit p.2, 1 - p.2)) = false} := by
  have hm : MeasurableSet {ω : EdgeField | ω (baseEdge p) = true} :=
    by
      change MeasurableSet ((fun ω : EdgeField => ω (baseEdge p)) ⁻¹' ({true} : Set Bool))
      exact (measurableSet_singleton true).preimage (measurable_pi_apply _)
  have h := congrArg (fun m : Measure EdgeField => m {ω | ω (baseEdge p) = true})
    squareLatticeUST_dual_law
  simp only [Measure.map_apply measurable_dualField hm] at h
  rw [← h]
  congr 1
  ext ω
  simp [dualField_baseEdge]

theorem squareLatticeUST_edge_add_dual (p : Site 2 × Fin 2) :
    (squareLatticeUST : Measure EdgeField) {ω | ω (baseEdge p) = true} +
      (squareLatticeUST : Measure EdgeField)
        {ω | ω (baseEdge (p.1 + unit p.2, 1 - p.2)) = true} = 1 := by
  have hm : MeasurableSet {ω : EdgeField | ω (baseEdge (p.1 + unit p.2, 1 - p.2)) = true} :=
    by
      change MeasurableSet ((fun ω : EdgeField => ω (baseEdge (p.1 + unit p.2, 1-p.2))) ⁻¹'
        ({true} : Set Bool))
      exact (measurableSet_singleton true).preimage (measurable_pi_apply _)
  have hc : {ω : EdgeField | ω (baseEdge (p.1 + unit p.2, 1 - p.2)) = false} =
      {ω : EdgeField | ω (baseEdge (p.1 + unit p.2, 1 - p.2)) = true}ᶜ := by
    ext ω; simp
  rw [squareLatticeUST_edge_dual p, hc, add_comm, measure_add_measure_compl hm]
  exact measure_univ

end
end FiniteAvalanches.Trees.Lattice
