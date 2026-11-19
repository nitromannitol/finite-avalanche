import FiniteAvalanches.Support.Plane.TwoArcJordan
import FiniteAvalanches.Support.Plane.JordanDrawingFaces
import FiniteAvalanches.Support.Plane.EdgeNoPathFaces
import FiniteAvalanches.Support.Plane.PathEdgeIncidence

/-!
# Edge-path duality from a simple selected path

An injective selected-edge path and an omitted non-loop edge form a Jordan
curve and prevent a dual path between the edge's chart faces.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST DrawingContraction Set
open scoped Classical

/-- A simple selected-edge path between the endpoints of an omitted non-loop
edge prevents dual reachability between its chart sides. -/
theorem not_dual_reaches_of_selected_simple_path {V E : Type}
    [Fintype V] [Fintype E] [Nonempty E] {G : CopiedGraph V E}
    (D : Drawing G) (charts : ∀ e, EdgeChart D e) (A : Finset E) (e : E)
    (he : e ∉ A) (hne : G.left e ≠ G.right e)
    (q : Path (D.point (G.left e)) (D.point (G.right e))) (hq : Function.Injective q)
    (hqtrace : range q ⊆ D.trace Set.univ A) :
    ¬ (⟨fun e => negativeChartFace D e (charts e),
      fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches
        (Aᶜ.erase e) (negativeChartFace D e (charts e)) (positiveChartFace D e (charts e)) := by
  let p : Path (D.point (G.left e)) (D.point (G.right e)) :=
    ⟨⟨D.curve e, D.continuous e⟩, D.start e, D.finish e⟩
  have hp : Function.Injective p := D.nonloop_curve_injective e hne
  have hmeet : range p ∩ range q = {D.point (G.left e), D.point (G.right e)} := by
    apply subset_antisymm
    · rintro z ⟨⟨t, ht⟩, hzq⟩
      exact D.trace_inter_omitted_edge A e he ⟨hqtrace hzq, ⟨t, ht⟩⟩
    · rintro z (rfl | rfl)
      · exact ⟨⟨0, p.source⟩, ⟨0, q.source⟩⟩
      · exact ⟨⟨1, p.target⟩, ⟨1, q.target⟩⟩
  let H := euclideanPlaneHomeomorph
  let C := H '' (range p ∪ range q)
  have hC : Schoenflies.IsSeparating C :=
    Schoenflies.jordan_curve_theorem (isJordanCurve_of_two_paths p q hp hq hmeet)
  have hCR : C ⊆ H '' drawingTrace (edgeSetDrawing D (insert e A)) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    rw [drawingTrace_edgeSetDrawing]
    rcases hz with ⟨t, rfl⟩ | hzq
    · exact Or.inr ⟨e, Finset.mem_insert_self e A, t, rfl⟩
    · rcases hqtrace hzq with ⟨v, hv, hvz⟩ | ⟨f, hf, t, hft⟩
      · exact Or.inl ⟨v, hv, hvz⟩
      · exact Or.inr ⟨f, Finset.mem_insert_of_mem hf, t, hft⟩
  have hmC : H (D.curve e ⟨1 / 2, by constructor <;> norm_num⟩) ∈ C :=
    ⟨_, Or.inl ⟨⟨1 / 2, by constructor <;> norm_num⟩, rfl⟩, rfl⟩
  have hneq := projected_chart_faces_ne_of_jordan D (edgeSetDrawing D (insert e A))
    (edgeSetDrawing_trace_subset D (insert e A)) charts e C hC hCR hmC
  intro hdual
  exact hneq ((edge_dual_reaches_iff_projected_faces_eq D charts A e).mp hdual)

/-- Edge-path duality reduces to finding simple paths in the selected drawing
between connected endpoints of omitted non-loop edges. -/
theorem edge_path_duality_of_selected_simple_paths {V E : Type}
    [Fintype V] [Fintype E] [Nonempty E] {G : CopiedGraph V E}
    (D : Drawing G) (charts : ∀ e, EdgeChart D e)
    (hsimple : ∀ (A : Finset E) e, e ∉ A → G.left e ≠ G.right e →
      G.reaches A (G.left e) (G.right e) →
      ∃ q : Path (D.point (G.left e)) (D.point (G.right e)),
        Function.Injective q ∧ range q ⊆ D.trace Set.univ A) :
    ∀ (A : Finset E) e, e ∉ A →
      (G.reaches A (G.left e) (G.right e) ↔
        ¬ (⟨fun e => negativeChartFace D e (charts e),
          fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches
          (Aᶜ.erase e) (negativeChartFace D e (charts e)) (positiveChartFace D e (charts e))) := by
  intro A e he
  by_cases hloop : G.left e = G.right e
  · exact edge_path_duality_of_loop D charts A e hloop
  · constructor
    · intro h
      obtain ⟨q, hq, hqt⟩ := hsimple A e he hloop h
      exact not_dual_reaches_of_selected_simple_path D charts A e he hloop q hq hqt
    · intro h
      by_contra hn
      exact h (dual_reaches_of_not_primal_reaches D charts A e he hn)

end FiniteAvalanches.Electrical.StatementGeometry
