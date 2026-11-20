import FiniteAvalanches.Support.Plane.SelectedGraph
import FiniteAvalanches.Support.Plane.JordanLoopExtension
import FiniteAvalanches.Support.Schoenflies.Graph.CycleJordan
import Mathlib.Combinatorics.Graph.Maps

/-!
# The drawing of the selected nonloop graph

A copied plane drawing induces a drawing of its selected nonloop multigraph.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval
open scoped Classical Graph

variable {V E : Type} [Fintype V] [Fintype E] {G : CopiedGraph V E}

/-- The path that parametrizes a copied edge. -/
def Drawing.edgePath (D : Drawing G) (e : E) : Path (D.point (G.left e)) (D.point (G.right e)) :=
  ⟨⟨D.curve e, D.continuous e⟩, D.start e, D.finish e⟩

/-- The copied edge parametrizations in Euclidean plane coordinates. -/
noncomputable def Drawing.selectedEdgeDrawing (D : Drawing G) (e : E) : ℝ → Schoenflies.Plane :=
  euclideanPlaneHomeomorph ∘ (D.edgePath e).extend

/-- Each drawn edge arc is the image of the copied edge curve. -/
theorem Drawing.selectedEdgeDrawing_arc (D : Drawing G) (e : E) :
    Graph.edgeArc D.selectedEdgeDrawing e = euclideanPlaneHomeomorph '' range (D.curve e) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨D.curve e ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩, ?_⟩
    simp only [selectedEdgeDrawing, Function.comp_apply, Path.extend_apply _ ht]
    rfl
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨t.val, t.property, ?_⟩
    simp only [selectedEdgeDrawing, Function.comp_apply, Path.extend_apply _ t.property]
    rfl

/-- A selected nonloop edge has its prescribed endpoints in the selected graph. -/
theorem CopiedGraph.selectedGraph_link (G : CopiedGraph V E) (A : Finset E)
    {e : E} (he : e ∈ A) (hn : G.left e ≠ G.right e) :
    (G.selectedGraph A).IsLink e (G.left e) (G.right e) :=
  ⟨he, hn, Or.inl ⟨rfl, rfl⟩⟩

/-- A vertex on a selected edge is one of its endpoints and is incident to it. -/
theorem Drawing.selectedGraph_vertex_on_edge (D : Drawing G) (A : Finset E)
    {e : E} (he : e ∈ A) (hn : G.left e ≠ G.right e) {v : V}
    (hv : euclideanPlaneHomeomorph (D.point v) ∈ Graph.edgeArc D.selectedEdgeDrawing e) :
    (v = G.left e ∨ v = G.right e) ∧
      ((G.selectedGraph A).map (euclideanPlaneHomeomorph ∘ D.point)).Inc e
        (euclideanPlaneHomeomorph (D.point v)) := by
  rw [D.selectedEdgeDrawing_arc] at hv
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hv
  have h := (D.curve_vertex_iff e t v).mp (euclideanPlaneHomeomorph.injective ht)
  have hl := G.selectedGraph_link A he hn
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨Or.inl rfl, hl.inc_left.map _⟩
  · exact ⟨Or.inr rfl, hl.inc_right.map _⟩

/-- The selected nonloop graph inherits the plane drawing. -/
theorem Drawing.selectedGraph_isDrawing (D : Drawing G) (A : Finset E) :
    Graph.IsDrawing ((G.selectedGraph A).map (euclideanPlaneHomeomorph ∘ D.point))
      D.selectedEdgeDrawing := by
  let H := euclideanPlaneHomeomorph ∘ D.point
  let K := (G.selectedGraph A).map H
  have hlink : ∀ {e : E}, e ∈ A → G.left e ≠ G.right e →
      K.IsLink e (H (G.left e)) (H (G.right e)) := by
    intro e he hn
    exact (G.selectedGraph_link A he hn).map H
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    have he' : e ∈ A ∧ G.left e ≠ G.right e := he
    refine ⟨(euclideanPlaneHomeomorph.continuous.comp (D.edgePath e).continuous_extend).continuousOn,
      ?_, ?_⟩
    · intro s hs t ht hst
      simp only [selectedEdgeDrawing, Function.comp_apply, Path.extend_apply _ hs,
        Path.extend_apply _ ht] at hst
      exact congrArg Subtype.val
        (D.nonloop_curve_injective e he'.2 (euclideanPlaneHomeomorph.injective hst))
    · change K.IsLink e (euclideanPlaneHomeomorph ((D.edgePath e).extend 0))
        (euclideanPlaneHomeomorph ((D.edgePath e).extend 1))
      rw [Path.extend_zero, Path.extend_one]
      exact hlink he'.1 he'.2
  · intro e x y z hl hz hze
    obtain ⟨v, -, rfl⟩ := hz
    have he : e ∈ A ∧ G.left e ≠ G.right e := hl.edge_mem
    obtain ⟨_, hi⟩ := D.selectedGraph_vertex_on_edge A he.1 he.2 hze
    exact hi.eq_or_eq_of_isLink hl
  · intro e f he hf hef z hze hzf
    have he' : e ∈ A ∧ G.left e ≠ G.right e := he
    have hf' : f ∈ A ∧ G.left f ≠ G.right f := hf
    rw [D.selectedEdgeDrawing_arc] at hze hzf
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ := hze
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hzf
    have hst : D.curve e s = D.curve f t := euclideanPlaneHomeomorph.injective (hs.trans ht.symm)
    rcases (D.intersects e f hef s t hst).1 with hs0 | hs1
    · have hs' : s = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext hs0
      have hz : z = H (G.left e) := by rw [← hs, hs', D.start]; rfl
      rw [hz]
      refine ⟨⟨G.left e, mem_univ _, rfl⟩, (hlink he'.1 he'.2).inc_left, ?_⟩
      apply (D.selectedGraph_vertex_on_edge A hf'.1 hf'.2 ?_).2
      rw [D.selectedEdgeDrawing_arc]
      exact ⟨D.curve f t, ⟨t, rfl⟩, (ht.trans hz)⟩
    · have hs' : s = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hs1
      have hz : z = H (G.right e) := by rw [← hs, hs', D.finish]; rfl
      rw [hz]
      refine ⟨⟨G.right e, mem_univ _, rfl⟩, (hlink he'.1 he'.2).inc_right, ?_⟩
      apply (D.selectedGraph_vertex_on_edge A hf'.1 hf'.2 ?_).2
      rw [D.selectedEdgeDrawing_arc]
      exact ⟨D.curve f t, ⟨t, rfl⟩, (ht.trans hz)⟩

end FiniteAvalanches.Electrical.StatementGeometry
