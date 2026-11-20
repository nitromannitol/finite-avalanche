import FiniteAvalanches.Trees.Lattice.Dual
import FiniteAvalanches.Wilson.Lattice.PositiveCylinder

/-! Finite-cylinder reduction for square-lattice duality. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- The original edge crossed by a dual lattice edge. -/
def crossingEdgeEquiv : LatticeEdge ≃ LatticeEdge :=
  edgeEquiv.symm.trans (dualBaseEquiv.trans edgeEquiv)

/-- Duality complements the value of the crossed original edge. -/
theorem dualField_apply_crossing (ω : EdgeField) (e : LatticeEdge) :
    dualField ω e = !ω (crossingEdgeEquiv e) := rfl

/-- The dual edge-field map is continuous for the product topology. -/
theorem continuous_dualField : Continuous dualField := by
  apply continuous_pi
  intro e
  change Continuous (fun ω : EdgeField => !ω (crossingEdgeEquiv e))
  exact (continuous_of_discreteTopology : Continuous (Bool.not : Bool → Bool)).comp
    (continuous_apply (crossingEdgeEquiv e))

/-- The finite family of original edges crossed by a finite dual family. -/
def crossingEdges (E : Finset LatticeEdge) : Finset LatticeEdge :=
  E.map crossingEdgeEquiv.toEmbedding

/-- The complementary primal pattern corresponding to a dual pattern. -/
def crossingPattern (E : Finset LatticeEdge) (p : E → Bool) : crossingEdges E → Bool :=
  fun e => !p ⟨crossingEdgeEquiv.symm e.val, by
    have he : e.val ∈ E.map crossingEdgeEquiv.toEmbedding := e.property
    simpa only [Finset.mem_map_equiv] using he⟩

/-- A dual cylinder is the corresponding complemented primal cylinder. -/
theorem dualField_preimage_cylinder (E : Finset LatticeEdge) (p : E → Bool) :
    dualField ⁻¹' cylinder E p = cylinder (crossingEdges E) (crossingPattern E p) := by
  ext ω
  simp only [Set.mem_preimage, FiniteAvalanches.Trees.Lattice.cylinder, Set.mem_setOf_eq, Finset.restrict_def, funext_iff]
  constructor
  · intro h e
    have he := h ⟨crossingEdgeEquiv.symm e.val, by
      have hm : e.val ∈ E.map crossingEdgeEquiv.toEmbedding := e.property
      simpa only [Finset.mem_map_equiv] using hm⟩
    simp only [dualField_apply_crossing, crossingEdgeEquiv.apply_symm_apply] at he
    simpa only [crossingPattern, Bool.not_not] using congrArg Bool.not he
  · intro h e
    have hm : crossingEdgeEquiv e.val ∈ crossingEdges E := by
      exact Finset.mem_map.mpr ⟨e.val, e.property, rfl⟩
    have he := h ⟨crossingEdgeEquiv e.val, hm⟩
    simp only [crossingPattern, crossingEdgeEquiv.symm_apply_apply] at he
    simp only [dualField_apply_crossing, he, Bool.not_not]

/-- Dual finite-cylinder probabilities are primal complemented-cylinder probabilities. -/
theorem finiteLaw_dual_cylinder (N : ℕ) (E : Finset LatticeEdge) (p : E → Bool) :
    (finiteLaw N).map dualField (cylinder E p) =
      finiteLaw N (cylinder (crossingEdges E) (crossingPattern E p)) := by
  rw [Measure.map_apply measurable_dualField (measurableSet_cylinder E p),
    dualField_preimage_cylinder]

/-- Self-duality of a weak wired limit reduces to equality of the limiting
probabilities of each finite pattern and its complemented crossing pattern. -/
theorem wiredLimit_dual_of_cylinder_limits (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν))
    (hcross : ∀ (E : Finset LatticeEdge) (p : E → Bool),
      Tendsto (fun N => finiteLaw N (cylinder (crossingEdges E) (crossingPattern E p)))
        atTop (nhds ((ν : Measure EdgeField) (cylinder E p)))) :
    (ν : Measure EdgeField).map dualField = (ν : Measure EdgeField) := by
  let νdual := ν.map measurable_dualField.aemeasurable
  apply congrArg (fun μ : ProbabilityMeasure EdgeField => (μ : Measure EdgeField))
    (probabilityMeasure_edgeField_eq_of_cylinder νdual ν ?_)
  intro E p
  have hweak := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    finiteProbability ν hν continuous_dualField
  have hmass := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hweak (E := cylinder E p) (by
      rw [(isClopen_cylinder E p).frontier_eq]
      exact measure_empty)
  have heq : (fun N => ((finiteProbability N).map continuous_dualField.measurable.aemeasurable :
      Measure EdgeField) (cylinder E p)) =
      (fun N => finiteLaw N (cylinder (crossingEdges E) (crossingPattern E p))) := by
    funext N
    exact finiteLaw_dual_cylinder N E p
  rw [heq] at hmass
  exact tendsto_nhds_unique hmass (hcross E p)


/-- Equality of limiting inclusion probabilities with crossed-edge avoidance
probabilities suffices for self-duality of the wired limit. -/
theorem wiredLimit_dual_of_inclusion_limits (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν))
    (hcross : ∀ E : Finset LatticeEdge,
      Tendsto (fun N => finiteLaw N
        (cylinder (crossingEdges E) (crossingPattern E (fun _ => true))))
        atTop (nhds ((ν : Measure EdgeField) (edgeInclusionEvent E)))) :
    (ν : Measure EdgeField).map dualField = (ν : Measure EdgeField) := by
  let νdual := ν.map measurable_dualField.aemeasurable
  apply congrArg (fun μ : ProbabilityMeasure EdgeField => (μ : Measure EdgeField))
    (probabilityMeasure_edgeField_eq_of_inclusion νdual ν ?_)
  intro E
  rw [edgeInclusionEvent_eq_cylinder]
  have hweak := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    finiteProbability ν hν continuous_dualField
  have hmass := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hweak (E := FiniteAvalanches.Trees.Lattice.cylinder E (fun _ => true)) (by
      rw [(isClopen_cylinder E (fun _ => true)).frontier_eq]
      exact measure_empty)
  have heq : (fun N => ((finiteProbability N).map continuous_dualField.measurable.aemeasurable :
      Measure EdgeField) (FiniteAvalanches.Trees.Lattice.cylinder E (fun _ => true))) =
      (fun N => finiteLaw N (cylinder (crossingEdges E) (crossingPattern E (fun _ => true)))) := by
    funext N
    exact finiteLaw_dual_cylinder N E (fun _ => true)
  rw [heq] at hmass
  have htarget := hcross E
  rw [edgeInclusionEvent_eq_cylinder] at htarget
  exact tendsto_nhds_unique hmass htarget

end
end FiniteAvalanches.Wilson.Lattice
