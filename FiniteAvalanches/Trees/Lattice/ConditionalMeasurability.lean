import FiniteAvalanches.Trees.Lattice.ConditionalObjects
import FiniteAvalanches.Trees.Lattice.TreeContinuityMeasurability

set_option autoImplicit false
open LatticeProb MeasureTheory ProbabilityTheory FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
namespace IndependentConditional10
noncomputable section

/-- The named outcome law is exactly the existing source ended UST, not a selection. -/
theorem original_ended_law : treeOutcomeLaw = TreeMeasurability11.endedUST := rfl

/-- All original measurable field events retain their actual UST probability. -/
theorem original_field_event (A : Set EdgeField) (hA : MeasurableSet A) :
    treeOutcomeLaw {t | t.val ∈ A} = (squareLatticeUST : Measure EdgeField) A := by
  have h := congrArg (fun μ : Measure EdgeField => μ A) treeOutcomeLaw_map_coe
  rw [Measure.map_apply measurable_subtype_coe hA] at h
  exact h

theorem measurable_actual_branch (S : Finset (Site 2)) (hS : S.Nonempty) :
    Measurable (connectingBranchField S hS) := by
  apply measurable_pi_lambda
  intro e
  have hω : Measurable (fun t : TreeOutcome => t.val e) :=
    (measurable_pi_apply e).comp measurable_subtype_coe
  have hd : Measurable (fun t : TreeOutcome => decide (∀ v ∈ e.val,
      v ∈ connectingSites t.val t.property.1 t.property.2 S hS)) :=
    (measurable_of_countable (fun K : Finset (Site 2) => decide (∀ v ∈ e.val, v ∈ K))).comp
      (TreeMeasurability11.measurable_connectingSites S hS)
  exact (measurable_of_countable (fun p : Bool × Bool => p.1 && p.2)).comp (hω.prodMk hd)

theorem measurable_actual_pair (S : Finset (Site 2)) (hS : S.Nonempty) :
    Measurable (fun t : TreeOutcome => sourceConnectingPair t.val t.property.1 t.property.2 S hS) := by
  have hs := TreeMeasurability11.measurable_connectingSites S hS
  have hr : Measurable (fun t : TreeOutcome =>
      (orientedRay t.val t.property.1 t.property.2
        (earliestCommonAncestor t.val t.property.1 t.property.2 S hS)).vertex) := by
    apply measurable_pi_lambda
    intro n
    have hm : Measurable (fun p : TreeOutcome × Site 2 =>
        (orientedRay p.1.val p.1.property.1 p.1.property.2 p.2).vertex n) :=
      measurable_from_prod_countable_left (fun x => TreeMeasurability11.measurable_rayVertex x n)
    exact hm.comp (measurable_id.prodMk (TreeMeasurability11.measurable_earliestCommonAncestor S hS))
  exact measurable_comap_iff.mpr (hs.prodMk hr)

/-- Complete observation measurability is derived from genuine branch/ray proofs. -/
theorem measurable_actual_observation (S : Finset (Site 2)) (hS : S.Nonempty) :
    Measurable (sourceObservation S hS) :=
  ((measurable_actual_branch S hS).prodMk (measurable_actual_pair S hS)).subtype_mk

theorem measurable_actual_count (S : Finset (Site 2)) (hS : S.Nonempty) :
    Measurable (sourceCount S hS) :=
  TreeMeasurability11.measurable_sourceBoundaryCount S hS

/-- The conditioning sigma field includes every actual selected branch edge. -/
theorem edge_observation_event (S : Finset (Site 2)) (hS : S.Nonempty) (e : LatticeEdge) :
    MeasurableSet {b : BranchObservation | b.val.1 e = true} ∧
      (sourceObservation S hS) ⁻¹' {b : BranchObservation | b.val.1 e = true} =
        {t : TreeOutcome | t.val e = true ∧ ∀ v ∈ e.val,
          v ∈ connectingSites t.val t.property.1 t.property.2 S hS} := by
  constructor
  · exact (measurableSet_singleton true).preimage
      ((measurable_pi_apply e).comp (measurable_fst.comp measurable_subtype_coe))
  · ext t
    exact connectingBranchField_eq_true_iff S hS t e

theorem actual_count_roots_and_full_law (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : TreeOutcome) (n : ℕ) (D : Set ℕ) :
    (sourceObservation S hS t).val.2.roots.zero =
      (connectingSites t.val t.property.1 t.property.2 S hS : Set (Site 2)) ∧
    (sourceObservation S hS t).val.2.roots.one =
      (orientedRay t.val t.property.1 t.property.2
        (earliestCommonAncestor t.val t.property.1 t.property.2 S hS)).tailVertices ∧
    ((sourceObservation S hS t).val.2.ray.vertex n ∈
      (sourceObservation S hS t).val.2.sites ↔ n = 0) ∧
    sourceCount S hS t = contacts
      (connectingSites t.val t.property.1 t.property.2 S hS)
      (fun y => decide (y ∉ cutComponent t.val
        (outgoingEdge t.val t.property.1 t.property.2
          (earliestCommonAncestor t.val t.property.1 t.property.2 S hS))
        (earliestCommonAncestor t.val t.property.1 t.property.2 S hS))) ∧
    branchCountLaw (sourceObservation S hS t) Set.univ = 1 ∧
    branchCountLaw (sourceObservation S hS t) D =
      wilsonColorLaw (sourceConnectingPair t.val t.property.1 t.property.2 S hS).roots
        {σ | contacts (connectingSites t.val t.property.1 t.property.2 S hS) σ ∈ D} :=
  ⟨rfl,rfl,(sourceObservation S hS t).val.2.ray_mem_iff n,rfl,measure_univ,
    actual_source_branch_law_all_counts S hS t D⟩

/-- The empty connecting tree for a singleton still records the true outgoing ray. -/
theorem singleton_observation (x : Site 2) (t : TreeOutcome) :
    (sourceObservation {x} (Finset.singleton_nonempty x) t).val.2.sites = {x} ∧
    Measurable (sourceObservation {x} (Finset.singleton_nonempty x)) :=
  ⟨sourceObservation_singleton x t,measurable_actual_observation _ _⟩

end
end IndependentConditional10
