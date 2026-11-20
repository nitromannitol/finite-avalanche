import FiniteAvalanches.Wilson.Lattice.FiniteUstCylinderConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Weak convergence of wired spanning trees from their finite edge cylinders. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice
open scoped Classical ENNReal

noncomputable section

/-- Probability measures on edge fields are determined by finite cylinders. -/
theorem probabilityMeasure_edgeField_eq_of_cylinder (μ ν : ProbabilityMeasure EdgeField)
    (h : ∀ (E : Finset LatticeEdge) (p : E → Bool),
      (μ : Measure EdgeField) (cylinder E p) = (ν : Measure EdgeField) (cylinder E p)) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  have hm (E : Finset LatticeEdge) :
      Measure.map E.restrict (μ : Measure EdgeField) = Measure.map E.restrict (ν : Measure EdgeField) := by
    apply Measure.ext_of_singleton
    intro p
    have hf : Measurable (E.restrict : EdgeField → E → Bool) :=
      measurable_pi_lambda _ (fun e => measurable_pi_apply e.val)
    rw [Measure.map_apply hf (measurableSet_singleton p),
      Measure.map_apply hf (measurableSet_singleton p)]
    exact h E p
  apply Measure.ext_of_generateFrom_of_iUnion
    (measurableCylinders (fun _ : LatticeEdge => Bool)) (fun _ : ℕ => (Set.univ : Set EdgeField))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (Set.iUnion_const _) (fun _ => univ_mem_measurableCylinders _) (fun _ => measure_ne_top _ _)
  intro S hS
  obtain ⟨E, A, hA, rfl⟩ := (mem_measurableCylinders S).mp hS
  have hf : Measurable (E.restrict : EdgeField → E → Bool) :=
    measurable_pi_lambda _ (fun e => measurable_pi_apply e.val)
  simpa only [Measure.map_apply hf hA, MeasureTheory.cylinder] using congrArg (fun m => m A) (hm E)

/-- Every weak cluster point has the limiting finite-cylinder probabilities. -/
theorem finiteProbability_clusterPoint_cylinder (ν : ProbabilityMeasure EdgeField)
    (hν : MapClusterPt ν atTop finiteProbability) (E : Finset LatticeEdge) (p : E → Bool)
    (a : ℝ≥0∞) (ha : Tendsto (fun B => finiteLaw B (cylinder E p)) atTop (nhds a)) :
    (ν : Measure EdgeField) (cylinder E p) = a := by
  obtain ⟨U, hU, hweak⟩ := mapClusterPt_iff_ultrafilter.mp hν
  have hfinite := ha.mono_left hU
  have hcluster := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hweak (E := cylinder E p) (by
      rw [(isClopen_cylinder E p).frontier_eq]
      exact measure_empty)
  exact tendsto_nhds_unique hcluster hfinite

/-- Finite wired spanning-tree laws have a weak limit on the full lattice
edge field. -/
theorem finiteProbability_exists_weak_limit :
    ∃ ν : ProbabilityMeasure EdgeField, Tendsto finiteProbability atTop (nhds ν) := by
  obtain ⟨ν, _, hν⟩ := (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure EdgeField))).exists_mapClusterPt
    (f := atTop) (u := finiteProbability) (by simp)
  refine ⟨ν, ?_⟩
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  apply probabilityMeasure_edgeField_eq_of_cylinder
  intro E p
  obtain ⟨a, ha⟩ := finiteLaw_cylinder_converges E p
  exact (finiteProbability_clusterPoint_cylinder μ hμ E p a ha).trans
    (finiteProbability_clusterPoint_cylinder ν hν E p a ha).symm

end
end FiniteAvalanches.Wilson.Lattice
