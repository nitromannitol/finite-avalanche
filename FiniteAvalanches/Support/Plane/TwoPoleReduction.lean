import FiniteAvalanches.Support.Plane.TwoPoleTreeComplement
import FiniteAvalanches.Support.Plane.BoundaryDartPermutation
import FiniteAvalanches.Electrical.Plane.Incidence

/-!
# Reduction of two-pole topology to the signed face boundary law

Finiteness of faces, polar connectivity, and tree complementation follow from
plane duality. The remaining input is the signed boundary of a primal gradient.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source Plane BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E]

/-- The two-pole topological conclusions follow from the signed face-boundary law. -/
theorem two_pole_topology_of_face_boundary {J : CopiedGraph V E} (D : PlaneEmbedding J)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : OuterArc D alpha beta)
    (hboundary : ∀ (q : V → ℝ) (F : A.embedding.Face),
      copyBoundary (augmentedDual A).left (augmentedDual A).right
        (copyGradient (augmentedGraph J alpha beta).left
          (augmentedGraph J alpha beta).right q) F = 0) :
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
  classical
  letI : Nonempty (E ⊕ Unit) := ⟨Sum.inr ()⟩
  letI : Finite A.embedding.Face := finite_faces_of_drawing A.embedding.drawing
  let finiteFaces := Fintype.ofFinite A.embedding.Face
  exact ⟨finiteFaces, polarGround_ne_polarSource D hconn alpha beta A,
    polarDual_preconnected D hconn alpha beta hne A,
    augmented_spanningTree_compl_iff D hconn alpha beta A finiteFaces, hboundary⟩

/-- The two-pole topological conclusions hold exactly when the augmented
edge ends can be matched at each vertex and face. -/
theorem two_pole_topology_iff_dart_permutation {J : CopiedGraph V E} (D : PlaneEmbedding J)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : OuterArc D alpha beta) :
    (∃ finiteFaces : Fintype A.embedding.Face,
      letI : Fintype A.embedding.Face := finiteFaces
      polarGround A ≠ polarSource A ∧
      (supportGraph (polarDual A).left (polarDual A).right).Preconnected ∧
      (∀ T : Finset (E ⊕ Unit),
        (∃ t : (augmentedGraph J alpha beta).SpanningTree, t.val = T) ↔
        (∃ t : (augmentedDual A).SpanningTree, t.val = Finset.univ \ T)) ∧
      (∀ (q : V → ℝ) (F : A.embedding.Face),
        copyBoundary (augmentedDual A).left (augmentedDual A).right
          (copyGradient (augmentedGraph J alpha beta).left
            (augmentedGraph J alpha beta).right q) F = 0)) ↔
    ∃ σ : Equiv.Perm ((E ⊕ Unit) × Bool),
      (∀ i, dartVertex (augmentedGraph J alpha beta).left
        (augmentedGraph J alpha beta).right (σ i) =
        dartVertex (augmentedGraph J alpha beta).left
          (augmentedGraph J alpha beta).right i) ∧
      (∀ i, dartPrevFace (augmentedDual A).left (augmentedDual A).right (σ i) =
        dartNextFace (augmentedDual A).left (augmentedDual A).right i) := by
  constructor
  · rintro ⟨_, _, _, _, hboundary⟩
    exact (copyBoundary_gradient_eq_zero_iff_dart_permutation _ _ _ _).mp hboundary
  · intro h
    apply two_pole_topology_of_face_boundary D hconn alpha beta hne A
    exact (copyBoundary_gradient_eq_zero_iff_dart_permutation _ _ _ _).mpr h

end FiniteAvalanches.Electrical.StatementGeometry
