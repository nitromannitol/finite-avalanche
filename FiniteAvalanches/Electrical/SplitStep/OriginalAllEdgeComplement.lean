import FiniteAvalanches.Electrical.SplitStep.ActualEnergy
import FiniteAvalanches.Electrical.ChordSplit.AllEdgeQuotient
import FiniteAvalanches.Electrical.Reference.ForestDualDictionary
import FiniteAvalanches.External.PlaneTreeComplement

/-! Complementary trees on the full original-copy root quotient and full-face deleted dual. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical
noncomputable section

local instance originalAllEdgeComplementCopyDec (D : Finset (Site 2))
    (P : OneSet D) (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) :=
  Classical.decEq _

/-- The original H0 with alpha and beta identified, keeping every original copied ID. -/
def originalAllEdgeQuotient (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :=
  NonemptyQuotient.allEdgeGraph (StatementTypes.graph D P marked)
    (pairRoots (alpha D P) (beta D P))

/-- Identifying just the two grounded terminals gives this quotient, at every split index. -/
theorem original_identify_grounded_graph (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    (⟨fun e => identifyGroundedTerminals (alpha D P) (beta D P) (K.left e),
      fun e => identifyGroundedTerminals (alpha D P) (beta D P) (K.right e)⟩ :
        CopiedGraph (NonemptyQuotient.Vertex (pairRoots (alpha D P) (beta D P)))
          (Copy D P marked)) = originalAllEdgeQuotient D P marked :=
  identify_grounded_graph (StatementTypes.graph D P marked) (alpha D P) (beta D P) _

/-- The registered original tree dictionary gives tree complementation for every copied subset.
Root-root copies remain loops in Y; all original faces and the supplied charts remain in B. -/
theorem original_allEdge_tree_complement_iff
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ A : Finset (Copy D P marked),
      ((Set.univ : Set (NonemptyQuotient.Vertex (pairRoots (alpha D P) (beta D P)))).Nonempty ∧
        (∀ x y, (originalAllEdgeQuotient D P marked).reaches A x y) ∧
        ∀ e ∈ A, ¬(originalAllEdgeQuotient D P marked).reaches (A.erase e)
          ((originalAllEdgeQuotient D P marked).left e)
          ((originalAllEdgeQuotient D P marked).right e)) ↔
      ((Set.univ : Set (Face Q)).Nonempty ∧
        (∀ x y, (sourceDeletedDualGraph D P marked Q charts).reaches Aᶜ x y) ∧
        ∀ e ∈ Aᶜ, ¬(sourceDeletedDualGraph D P marked Q charts).reaches (Aᶜ.erase e)
          ((sourceDeletedDualGraph D P marked Q charts).left e)
          ((sourceDeletedDualGraph D P marked Q charts).right e)) := by
  letI : Fintype (Face Q) := finiteFaces
  intro A
  exact (NonemptyQuotient.allEdge_tree_iff_rooted_forest (StatementTypes.graph D P marked)
    (pairRoots (alpha D P) (beta D P)) A).trans
    (source_forest_dual_iff FiniteAvalanches.External.finite_plane_tree_complement
      D P hD marked Q charts finiteFaces A)

/-- The complement maps on all original IDs are actual inverse bijections. -/
def originalAllEdgeDualTreeEquiv
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    (originalAllEdgeQuotient D P marked).SpanningTree ≃
      (sourceDeletedDualGraph D P marked Q charts).SpanningTree := by
  letI : Fintype (Face Q) := finiteFaces
  let h := original_allEdge_tree_complement_iff D P hD marked Q charts finiteFaces
  exact {
    toFun := fun T => ⟨T.valᶜ, (h T.val).mp T.property⟩
    invFun := fun T => ⟨T.valᶜ, (h T.valᶜ).mpr (by
      simpa only [compl_compl] using T.property)⟩
    left_inv := fun T => Subtype.ext (compl_compl T.val)
    right_inv := fun T => Subtype.ext (compl_compl T.val) }

theorem originalAllEdgeDualTreeEquiv_copies
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ T : (originalAllEdgeQuotient D P marked).SpanningTree,
      (originalAllEdgeDualTreeEquiv D P hD marked Q charts finiteFaces T).val = T.valᶜ := by
  intro T
  rfl

end
end FiniteAvalanches.Electrical.SplitStep
