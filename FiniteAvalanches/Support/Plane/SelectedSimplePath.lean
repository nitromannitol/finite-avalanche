import FiniteAvalanches.Support.Plane.SelectedDrawing
import FiniteAvalanches.Support.Plane.SimplePathDuality

/-!
# Simple paths in selected drawings

Reachable distinct vertices in a copied plane drawing are joined by an
injective path in the selected trace.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval
open scoped Classical Graph

variable {V E : Type} [Fintype V] [Fintype E] {G : CopiedGraph V E}

/-- Mapping vertices of a graph maps walks to walks. -/
theorem graph_walk_map {α β γ : Type} {K : Graph α β} {u v : α} {W : List β}
    (f : α → γ) (h : K.IsWalk u W v) : (K.map f).IsWalk (f u) W (f v) := by
  induction h with
  | nil hu => exact .nil ⟨_, hu, rfl⟩
  | cons hl _ ih => exact .cons (hl.map f) ih

/-- Reachable distinct vertices are joined by an injective path in the selected trace. -/
theorem Drawing.exists_simple_path_of_reaches (D : Drawing G) (A : Finset E) {u v : V}
    (hne : u ≠ v) (h : G.reaches A u v) :
    ∃ q : Path (D.point u) (D.point v), Function.Injective q ∧
      range q ⊆ D.trace univ A := by
  let H := euclideanPlaneHomeomorph
  let F := H ∘ D.point
  let K := (G.selectedGraph A).map F
  obtain ⟨W, hW⟩ := G.selectedGraph_reaches A h
  have hR : K.Reaches (F u) (F v) := ⟨W, graph_walk_map F hW⟩
  obtain ⟨P, hP⟩ := hR.exists_isPath
  have hne' : F u ≠ F v := fun h => hne (D.point_injective (H.injective h))
  have hPne : P ≠ [] := hP.ne_nil hne'
  obtain ⟨f, hcont, hinj, him, hf0, hf1⟩ :=
    (D.selectedGraph_isDrawing A).path_isArcBetween hP hPne
  let q : Path (D.point u) (D.point v) :=
    ⟨⟨fun t => H.symm (f t), H.symm.continuous.comp (continuousOn_iff_continuous_restrict.mp hcont)⟩,
      by simpa [F, H] using congrArg H.symm hf0,
      by simpa [F, H] using congrArg H.symm hf1⟩
  refine ⟨q, ?_, ?_⟩
  · intro s t hst
    apply Subtype.ext
    exact hinj s.property t.property (H.symm.injective hst)
  · rintro z ⟨t, rfl⟩
    have hz : f t ∈ Graph.edgesCover D.selectedEdgeDrawing P := by
      rw [← him]
      exact ⟨t, t.property, rfl⟩
    obtain ⟨e, heP, hez⟩ := Graph.mem_edgesCover_iff.mp hz
    have he : e ∈ A ∧ G.left e ≠ G.right e := hP.edge_mem heP
    rw [D.selectedEdgeDrawing_arc] at hez
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ := hez
    right
    refine ⟨e, he.1, s, ?_⟩
    change D.curve e s = H.symm (f t)
    rw [← hs, Homeomorph.symm_apply_apply]

/-- The planar edge-path duality relation holds for every selected edge set. -/
theorem edge_path_duality {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    {G : CopiedGraph V E} (D : Drawing G)
    (charts : ∀ e, FiniteAvalanches.Electrical.Source.EdgeChart D e) :
    ∀ (A : Finset E) e, e ∉ A →
      (G.reaches A (G.left e) (G.right e) ↔
        ¬ (⟨fun e => FiniteAvalanches.Electrical.BSST.negativeChartFace D e (charts e),
          fun e => FiniteAvalanches.Electrical.BSST.positiveChartFace D e (charts e)⟩ :
            CopiedGraph (FiniteAvalanches.Electrical.BSST.Face D) E).reaches
          (Aᶜ.erase e) (FiniteAvalanches.Electrical.BSST.negativeChartFace D e (charts e))
          (FiniteAvalanches.Electrical.BSST.positiveChartFace D e (charts e))) := by
  apply edge_path_duality_of_selected_simple_paths D charts
  intro A e _ hne h
  exact D.exists_simple_path_of_reaches A hne h

end FiniteAvalanches.Electrical.StatementGeometry
