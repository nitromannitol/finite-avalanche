import FiniteAvalanches.Support.Plane.PolarDualConnected
import FiniteAvalanches.Support.Plane.UnchartedFaces
import FiniteAvalanches.External.PlaneTreeComplement

/-!
# Spanning-tree complements for a two-pole drawing

The general plane tree-complement theorem applies to the drawing augmented by
the physical outer arc, retaining every original copied edge.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E]

/-- A tree of the augmented drawing is complementary to a tree of its full dual. -/
theorem augmented_spanningTree_compl_iff {J : CopiedGraph V E} (D : PlaneEmbedding J)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (A : OuterArc D alpha beta)
    (finiteFaces : Fintype A.embedding.Face) :
    letI : Fintype A.embedding.Face := finiteFaces
    ∀ T : Finset (E ⊕ Unit),
      (∃ t : (augmentedGraph J alpha beta).SpanningTree, t.val = T) ↔
      (∃ t : (augmentedDual A).SpanningTree, t.val = Finset.univ \ T) := by
  classical
  letI : DecidableEq (E ⊕ Unit) := Classical.decEq _
  letI : Fintype A.embedding.Face := finiteFaces
  let B := augmentedGraph J alpha beta
  let K := augmentedDual A
  have hB : ∀ x y, B.reaches Finset.univ x y := by
    intro x y
    have h := J.reaches_augmented_original alpha beta
      (J.reaches_univ_of_supportGraph_reachable (hconn x y))
    exact B.reaches_mono (Finset.subset_univ _) h
  have hK : K = (⟨fun e => negativeChartFace A.embedding.drawing e (A.embedding.edgeChart e),
      fun e => positiveChartFace A.embedding.drawing e (A.embedding.edgeChart e)⟩ :
      CopiedGraph (Face A.embedding.drawing) (E ⊕ Unit)) := by
    congr 1
  intro T
  have h := FiniteAvalanches.External.finite_plane_tree_complement B A.embedding.drawing
    A.embedding.edgeChart ⟨alpha, mem_univ _⟩ hB finiteFaces T
  rw [← hK] at h
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨⟨_, h.mp t.property⟩, ?_⟩
    ext e
    simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_univ, true_and]
  · rintro ⟨t, ht⟩
    have ht' : t.val = Tᶜ := by
      ext e
      have hm := congrArg (fun S : Finset (E ⊕ Unit) => e ∈ S) ht
      simpa only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_univ, true_and] using (iff_of_eq hm)
    have hprop := ht' ▸ t.property
    exact ⟨⟨T, h.mpr hprop⟩, rfl⟩

end FiniteAvalanches.Electrical.StatementGeometry
