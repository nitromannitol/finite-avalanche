import FiniteAvalanches.Support.Plane.DeletedDualConnectivity
import FiniteAvalanches.Support.Plane.TreeComplementReduction

/-!
# Edge-path duality and face separation

For a selected edge set and one further edge, the deleted-edge dual-walk
correspondence reduces edge-path duality to separation of its two chart sides
in the retained subdrawing.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST DrawingContraction Set
open scoped Classical

/-- The copied graph retaining precisely a given finite set of edge copies. -/
def edgeSetGraph {V E : Type} (G : CopiedGraph V E) (A : Finset E) :
    CopiedGraph V {e : E // e ∈ A} :=
  ⟨fun e => G.left e, fun e => G.right e⟩

/-- The drawing retaining precisely the selected edge copies and all vertices. -/
def edgeSetDrawing {V E : Type} [Fintype V] [Fintype E]
    {G : CopiedGraph V E} (D : Drawing G) (A : Finset E) : Drawing (edgeSetGraph G A) :=
  restrictDrawing D Subtype.val Subtype.val_injective (fun _ => rfl) (fun _ => rfl)

/-- The retained drawing trace is contained in the full drawing trace. -/
theorem edgeSetDrawing_trace_subset {V E : Type} [Fintype V] [Fintype E]
    {G : CopiedGraph V E} (D : Drawing G) (A : Finset E) :
    drawingTrace (edgeSetDrawing D A) ⊆ drawingTrace D :=
  drawingTrace_restrictDrawing_subset D Subtype.val Subtype.val_injective
    (fun _ => rfl) (fun _ => rfl)

/-- The dual reachability condition for an edge is exactly equality of its
chart-side faces in the drawing retaining that edge and the chosen edges. -/
theorem edge_dual_reaches_iff_projected_faces_eq
    {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    {G : CopiedGraph V E} (D : Drawing G) (charts : ∀ e, EdgeChart D e)
    (A : Finset E) (e : E) :
    let R := edgeSetDrawing D (insert e A)
    let htrace := edgeSetDrawing_trace_subset D (insert e A)
    (⟨fun e => negativeChartFace D e (charts e),
      fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches
        (Aᶜ.erase e) (negativeChartFace D e (charts e)) (positiveChartFace D e (charts e)) ↔
    faceProjection D R htrace (negativeChartFace D e (charts e)) =
      faceProjection D R htrace (positiveChartFace D e (charts e)) := by
  have hS : ∀ f : E, f ∈ Aᶜ.erase e ↔
      f ∉ range (Subtype.val : {f : E // f ∈ insert e A} → E) := by
    intro f
    rw [Subtype.range_val_subtype]
    simp only [mem_setOf_eq, Finset.mem_erase, Finset.mem_compl, Finset.mem_insert, not_or]

  exact (faceProjection_eq_iff_dual_reaches_of_restrictDrawing D charts
    (Subtype.val : {f : E // f ∈ insert e A} → E) Subtype.val_injective
    (fun _ => rfl) (fun _ => rfl) (Aᶜ.erase e) hS _ _).symm

/-- Edge-path duality follows from separation of the two sides of each edge in
the retained subdrawing. -/
theorem edge_path_duality_of_face_separation
    {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    {G : CopiedGraph V E} (D : Drawing G) (charts : ∀ e, EdgeChart D e)
    (hsep : ∀ (A : Finset E) e, e ∉ A →
      (G.reaches A (G.left e) (G.right e) ↔
        let R := edgeSetDrawing D (insert e A)
        let htrace := edgeSetDrawing_trace_subset D (insert e A)
        faceProjection D R htrace (negativeChartFace D e (charts e)) ≠
          faceProjection D R htrace (positiveChartFace D e (charts e)))) :
    ∀ (A : Finset E) e, e ∉ A →
      (G.reaches A (G.left e) (G.right e) ↔
        ¬ (⟨fun e => negativeChartFace D e (charts e),
          fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches
          (Aᶜ.erase e) (negativeChartFace D e (charts e))
          (positiveChartFace D e (charts e))) := by
  intro A e he
  exact (hsep A e he).trans (not_congr (edge_dual_reaches_iff_projected_faces_eq D charts A e).symm)

end FiniteAvalanches.Electrical.StatementGeometry
