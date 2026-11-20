import FiniteAvalanches.Wilson.Lattice.WiredJointCylinders
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Ultrafilter

/-! Compactness and the joint-cylinder limits of finite wired forest laws. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Every weak cluster point of finite wired forest laws has the joint
cylinder probabilities of the finite recurrent Wilson sampler. -/
theorem clusterPoint_jointEvent_eq_sampler (R : RootPair) (ν : ProbabilityMeasure ForestField)
    (hν : MapClusterPt ν atTop (finiteForestProbability R)) (x : ℕ → Site 2) (n : ℕ)
    (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hD : ∀ z ∈ D, ∃ i < n, x i = z) :
    (ν : Measure ForestField) (jointEvent E D pe pc) =
      wilsonRows (samplerEvent R ((List.range n).map x) E D pe pc) := by
  obtain ⟨U, hU, hweak⟩ := mapClusterPt_iff_ultrafilter.mp hν
  have hfinite := (finiteForestLaw_jointEvent_tendsto R x (fun _ => 0) (fun _ _ => 0)
    n E D pe pc hE hD).mono_left hU
  have hcluster := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hweak (E := jointEvent E D pe pc) (by
      rw [(isClopen_jointEvent E D pe pc).frontier_eq]
      exact measure_empty)
  exact tendsto_nhds_unique hcluster hfinite

/-- Some probability measure has all finite joint-cylinder probabilities of
the recurrent Wilson sampler. -/
theorem exists_probabilityMeasure_jointEvent_eq_sampler (R : RootPair) :
    ∃ ν : ProbabilityMeasure ForestField, ∀ (x : ℕ → Site 2) (n : ℕ)
      (E : Finset LatticeEdge) (D : Finset (Site 2))
      (pe : LatticeEdge → Bool) (pc : Site 2 → Bool),
      (∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) →
      (∀ z ∈ D, ∃ i < n, x i = z) →
      (ν : Measure ForestField) (jointEvent E D pe pc) =
        wilsonRows (samplerEvent R ((List.range n).map x) E D pe pc) := by
  obtain ⟨ν, _, hν⟩ := (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure ForestField))).exists_mapClusterPt
    (f := atTop) (u := finiteForestProbability R) (by simp)
  exact ⟨ν, fun x n E D pe pc hE hD => clusterPoint_jointEvent_eq_sampler R ν hν x n E D pe pc hE hD⟩

end
end FiniteAvalanches.Wilson.Lattice
