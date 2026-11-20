import FiniteAvalanches.Wilson.Lattice.WiredDualFaceConnected
import FiniteAvalanches.Wilson.Lattice.FiniteDualLawTransfer

/-! The uniform tree law of the shifted dual face square. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceLaw (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- Extend a dual face tree by absent lattice edges outside its square. -/
def wiredDualFaceField {B : ℕ} (t : (wiredDualFaceGraph B).SpanningTree) : EdgeField :=
  fun e => decide (∃ q : FiniteWired.Edge B, q ∈ t.val ∧ wiredCopyDualEdge q = e)

/-- A represented dual edge is present exactly when its copy is in the face tree. -/
theorem wiredDualFaceField_copy_iff {B : ℕ} (t : (wiredDualFaceGraph B).SpanningTree)
    (q : FiniteWired.Edge B) :
    wiredDualFaceField t (wiredCopyDualEdge q) = true ↔ q ∈ t.val := by
  simp only [wiredDualFaceField, decide_eq_true_eq]
  constructor
  · rintro ⟨r, hr, he⟩
    exact (wiredCopyDualEdge_injective B he) ▸ hr
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- The uniform dual face tree, viewed as a lattice edge field. -/
def wiredDualFaceLaw (B : ℕ) : Measure EdgeField :=
  Measure.map (@wiredDualFaceField B) (wiredDualFaceGraph B).treeLaw

instance wiredDualFaceLaw_probability (B : ℕ) : IsProbabilityMeasure (wiredDualFaceLaw B) :=
  ((wiredDualFaceGraph B).treeLaw).isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- The dual face tree law as a probability measure. -/
def wiredDualFaceProbability (B : ℕ) : ProbabilityMeasure EdgeField :=
  ⟨wiredDualFaceLaw B, inferInstance⟩

/-- On an interior copy, complementary finite trees produce the same dual indicator. -/
theorem dualField_wiredField_eq_dualFaceField (B : ℕ)
    (t : (WiredTrees.graph B).SpanningTree) (u : (wiredDualFaceGraph B).SpanningTree)
    (hu : u.val = t.valᶜ) (i : FiniteWired.InteriorEdge B) :
    dualField (wiredField t) (wiredCopyDualEdge (.inl i)) =
      wiredDualFaceField u (wiredCopyDualEdge (.inl i)) := by
  rw [dualField_wiredCopyDualEdge, wiredCopyLatticeEdge_interior]
  have hp := wiredField_internal_iff t i
  have hd := wiredDualFaceField_copy_iff u (.inl i)
  rw [hu, Finset.mem_compl] at hd
  cases h : wiredField t (interiorEdge i) <;>
    cases k : wiredDualFaceField u (wiredCopyDualEdge (.inl i)) <;>
    simp_all

/-- A complementary-tree bijection transfers every cylinder whose crossed
primal edges have interior wired copies. -/
theorem finite_dual_cylinder_eq_dualFaceLaw_of_tree_equiv (B : ℕ)
    (φ : (WiredTrees.graph B).SpanningTree ≃ (wiredDualFaceGraph B).SpanningTree)
    (hφ : ∀ t, (φ t).val = t.valᶜ)
    (E : Finset LatticeEdge) (p : E → Bool)
    (hE : ∀ e ∈ E, ∃ i : FiniteWired.InteriorEdge B, wiredCopyDualEdge (.inl i) = e) :
    finiteLaw B (dualField ⁻¹' cylinder E p) = wiredDualFaceLaw B (cylinder E p) := by
  apply finite_dual_cylinder_of_tree_equiv B φ wiredDualFaceField E p
  intro t e he
  obtain ⟨i, rfl⟩ := hE e he
  exact dualField_wiredField_eq_dualFaceField B t (φ t) (hφ t) i

end
end FiniteAvalanches.Wilson.Lattice
