module

public import FiniteAvalanches.Sandpile.Burning.Vertices

@[expose] public section

/-! Total and every forbidden-subset degree on the literal graph carriers.
The proofs count exactly the unchanged original edge-copy IDs. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

theorem inside_graph_degree (B A : Finset (SourceVertex s)) (hBA : B ⊆ A)
    (x : InsideVertex s A) :
    degree (sourceHeldGraph G s B A hBA) (heldVertexEquiv s A x).val =
      if x.val ∈ B then degree G x.val.val else activeDegree G (Finset.univ.erase s) A x.val := by
  rw [held_vertex_equiv_val, source_held_degree]
  simp only [inside_vertex_equiv_val, activeDegree]
  simp only [← subtype_mem_image_iff (Finset.univ.erase s) B x.val]

theorem outside_graph_degree (A : Finset (SourceVertex s)) (x : OutsideVertex s A) :
    degree (complementGraph G s A) (outsideVertexEquiv s A x).val =
      degree G x.val.val - activeDegree G (Finset.univ.erase s) A x.val := by
  change degree (inducedGraph G (Finset.univ \ A.image Subtype.val))
    (outsideVertexEquiv s A x).val = _
  rw [degree_induced_compl]
  rfl

theorem inside_graph_active_degree (B A : Finset (SourceVertex s)) (hBA : B ⊆ A)
    (H : Finset (InsideVertex s A)) (x : InsideVertex s A) :
    activeDegree (sourceHeldGraph G s B A hBA) (Finset.univ.erase none)
        (H.image (heldVertexEquiv s A)) (heldVertexEquiv s A x) =
      activeDegree G (Finset.univ.erase s) (H.image Subtype.val) x.val := by
  have he : (H.image (heldVertexEquiv s A)).image Subtype.val =
      (H.image (insideVertexEquiv s A)).image some := by
    simp only [Finset.image_image]
    rfl
  unfold activeDegree
  rw [he, held_vertex_equiv_val]
  dsimp only [sourceHeldGraph]
  rw [degree_into_held_graph]
  simp only [Finset.image_image, inside_vertex_equiv_val]
  rfl

theorem outside_graph_active_degree (A : Finset (SourceVertex s))
    (H : Finset (OutsideVertex s A)) (x : OutsideVertex s A) :
    activeDegree (complementGraph G s A) (Finset.univ.erase (complementSink s A))
        (H.image (outsideVertexEquiv s A)) (outsideVertexEquiv s A x) =
      activeDegree G (Finset.univ.erase s) (H.image Subtype.val) x.val := by
  unfold activeDegree
  rw [Finset.image_image]
  change degreeInto (inducedGraph G (Finset.univ \ A.image Subtype.val))
    (H.image (fun y => (outsideVertexEquiv s A y).val)) (outsideVertexEquiv s A x).val = _
  rw [degree_into_induced_graph]
  simp only [Finset.image_image, outside_vertex_equiv_val]
  rfl

end
end FiniteAvalanches.Sandpile.Burning
