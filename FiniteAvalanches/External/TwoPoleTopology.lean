import FiniteAvalanches.Electrical.Geometry.PolarDual
import FiniteAvalanches.Support.Plane.FaceBoundaryLaw
import FiniteAvalanches.Support.Plane.TwoPoleReduction
import FiniteAvalanches.Support.Plane.UnchartedFaces

/-! Classical finite-plane two-pole topology, with every original copied edge.
The assertion concerns actual complementary regions of continuous embeddings.
Electrical consequences are ordinary proofs from this assertion and BSST. -/
set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source FiniteAvalanches.Electrical.Plane
open scoped Classical

/-- Actual finite faces, polar connectedness, copied tree complementation and
universal face-boundary telescoping for a given physical outer arc. -/
theorem finite_plane_two_pole_topology :
∀ {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (_hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (_hne : alpha ≠ beta) (A : OuterArc D alpha beta),
    ∃ finiteFaces : Fintype A.embedding.Face,
      letI : Fintype A.embedding.Face := finiteFaces
      polarGround A ≠ polarSource A ∧
      (supportGraph (polarDual A).left (polarDual A).right).Preconnected ∧
      (∀ T : Finset (E ⊕ Unit),
        (∃ t : (augmentedGraph J alpha beta).SpanningTree, t.val = T) ↔
        (∃ t : (augmentedDual A).SpanningTree, t.val = Finset.univ \ T)) ∧
      (∀ (q : V → ℝ) (F : A.embedding.Face),
        copyBoundary (augmentedDual A).left (augmentedDual A).right
          (copyGradient (augmentedGraph J alpha beta).left
            (augmentedGraph J alpha beta).right q) F = 0) := by
  intro V E _ _ J D hc alpha beta hne A
  apply two_pole_topology_of_face_boundary D hc alpha beta hne A
  intro q F
  letI : Nonempty (E ⊕ Unit) := ⟨Sum.inr ()⟩
  letI : Finite A.embedding.Face := finite_faces_of_drawing A.embedding.drawing
  letI : Fintype (BSST.Face A.embedding.drawing) := Fintype.ofFinite _
  have hB : ∀ x y, (augmentedGraph J alpha beta).reaches Finset.univ x y := by
    intro x y
    exact (augmentedGraph J alpha beta).reaches_mono (Finset.subset_univ _)
      (J.reaches_augmented_original alpha beta
        (J.reaches_univ_of_supportGraph_reachable (hc x y)))
  exact copyBoundary_chartFaces_gradient_eq_zero A.embedding.drawing A.embedding.edgeChart
    ⟨alpha, Set.mem_univ _⟩ hB q F

end FiniteAvalanches.External
