import FiniteAvalanches.Electrical.Geometry.PolarDual
import FiniteAvalanches.Electrical.Geometry.CopiedGraphConnectivity
import FiniteAvalanches.Support.Plane.SelectedSimplePath

/-!
# Separation of the two pole faces

The added arc joins vertices already connected by original copies. Edge-path
duality then separates the two faces along that arc.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- A walk in a copied graph lifts to its augmented graph using original copies. -/
theorem CopiedGraph.reaches_augmented_original (J : CopiedGraph V E) (alpha beta : V)
    {u v : V} (h : J.reaches Finset.univ u v) :
    (augmentedGraph J alpha beta).reaches (Finset.univ.image Sum.inl) u v := by
  induction h with
  | refl => exact .refl
  | tail _ hadj ih =>
    obtain ⟨e, he, hends⟩ := hadj
    apply ih.tail
    exact ⟨Sum.inl e, Finset.mem_image.mpr ⟨e, he, rfl⟩, hends⟩

/-- The two faces on the added arc are distinct when the original copied graph
is connected. -/
theorem polarGround_ne_polarSource {J : CopiedGraph V E} (D : PlaneEmbedding J)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (A : OuterArc D alpha beta) : polarGround A ≠ polarSource A := by
  classical
  let B := augmentedGraph J alpha beta
  let m : E ⊕ Unit := Sum.inr ()
  let T : Finset (E ⊕ Unit) := Finset.univ.image Sum.inl
  have hm : m ∉ T := by
    intro h
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
    simp only [m, Sum.inl_ne_inr] at he
  have hw : B.reaches T (B.left m) (B.right m) := by
    apply J.reaches_augmented_original alpha beta
    exact J.reaches_univ_of_supportGraph_reachable (hconn alpha beta)
  have hdual := (edge_path_duality A.embedding.drawing A.embedding.edgeChart T m hm).mp hw
  intro heq
  apply hdual
  have hf : negativeChartFace A.embedding.drawing m (A.embedding.edgeChart m) =
      positiveChartFace A.embedding.drawing m (A.embedding.edgeChart m) := heq
  rw [hf]
  exact .refl

end FiniteAvalanches.Electrical.StatementGeometry
