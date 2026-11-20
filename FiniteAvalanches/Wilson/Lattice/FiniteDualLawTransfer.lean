import FiniteAvalanches.Wilson.Lattice.DualCylinder
import FiniteAvalanches.Probability.UniformMap

/-! Transfer of finite uniform tree laws along a planar tree equivalence. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

local instance decEqWiredEdgeFiniteDualLawTransfer (N : ℕ) :
    DecidableEq (FiniteWired.Edge N) := Classical.decEq _

/-- An equivalence from wired trees to a finite dual-tree carrier that preserves
a finite edge observation transports the uniform cylinder probability. -/
theorem finite_dual_cylinder_of_tree_equiv (B : ℕ) {T : Type*} [Fintype T] [Nonempty T]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    (φ : (WiredTrees.graph B).SpanningTree ≃ T) (dualTreeField : T → EdgeField)
    (E : Finset LatticeEdge) (p : E → Bool)
    (hφ : ∀ t : (WiredTrees.graph B).SpanningTree, ∀ e ∈ E,
      dualField (wiredField t) e = dualTreeField (φ t) e) :
    finiteLaw B (dualField ⁻¹' cylinder E p) =
      (FiniteAvalanches.uniformMeasure T).map dualTreeField (cylinder E p) := by
  have hm : MeasurableSet (dualField ⁻¹' cylinder E p) :=
    (measurableSet_cylinder E p).preimage measurable_dualField
  rw [finiteLaw_apply B _ hm,
    Measure.map_apply (measurable_of_finite dualTreeField) (measurableSet_cylinder E p)]
  let A : Set T := {t | dualTreeField t ∈ cylinder E p}
  have hA : MeasurableSet A := A.toFinite.measurableSet
  have hevent : {t : (WiredTrees.graph B).SpanningTree | wiredField t ∈ dualField ⁻¹' cylinder E p} =
      φ ⁻¹' A := by
    ext t
    change dualField (wiredField t) ∈ cylinder E p ↔ dualTreeField (φ t) ∈ cylinder E p
    change E.restrict (dualField (wiredField t)) = p ↔ E.restrict (dualTreeField (φ t)) = p
    have hres : E.restrict (dualField (wiredField t)) = E.restrict (dualTreeField (φ t)) := by
      funext e
      exact hφ t e.val e.property
    rw [hres]
  rw [hevent]
  have hmap := FiniteAvalanches.uniform_measure_map_equiv φ
  have heq := congrArg (fun μ : Measure T => μ A) hmap
  rw [Measure.map_apply (measurable_of_finite φ) hA] at heq
  exact heq

end
end FiniteAvalanches.Wilson.Lattice
