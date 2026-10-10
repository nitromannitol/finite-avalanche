import FiniteAvalanches.Sandpile.Components.GraphFields
import FiniteAvalanches.Sandpile.Components.InducedRestriction
import FiniteAvalanches.Sandpile.Components.FieldTransport

/-! Canonical burning degrees on the literal induced copied lattice graphs.
Subset tests keep original copies and apply only to vertices of the tested subset. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Finset source exclusion is precisely the actual root inequality. -/
def sourceVertexEquiv {V : Type*} [Fintype V] [DecidableEq V] (s : V) :
    Burning.SourceVertex s ≃ {v : V // v ≠ s} :=
  Equiv.subtypeEquivRight fun v => by simp

def innerSourceVertexEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)} ≃
      Burning.SourceVertex (innerRoot C) :=
  (innerVertexEquiv C).symm.trans (sourceVertexEquiv (innerRoot C)).symm

def outerSourceVertexEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    {x : Site2 // x ∈ boxSites N \ C.val} ≃ Burning.SourceVertex (outerRoot C) :=
  (outerVertexEquiv C).symm.trans (sourceVertexEquiv (outerRoot C)).symm

theorem burning_degree_eq {N : ℕ} (V : Set (FiniteWired.Vertex N)) (v : V) :
    Burning.degree (inducedGraph V) v = graphDegree V v := by
  unfold Burning.degree Burning.degreeInto Burning.incidentInto graphDegree
  rw [Fintype.card_subtype]
  simp only [Finset.mem_univ, and_true]

theorem inner_source_degree {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)}) :
    Burning.degree (inducedGraph (insideSupport C)) (innerSourceVertexEquiv C x).val =
      degree C.val x.val := by
  rw [burning_degree_eq, inner_graph_degree_eq]
  exact congrArg (degree C.val) (congrArg Subtype.val ((innerVertexEquiv C).apply_symm_apply x))

theorem outer_source_degree {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (x : {x : Site2 // x ∈ boxSites N \ C.val}) :
    Burning.degree (inducedGraph (outsideSupport C)) (outerSourceVertexEquiv C x).val =
      4 - degree C.val x.val := by
  rw [burning_degree_eq]
  change graphDegree (outsideSupport C) ((outerVertexEquiv C).symm x).val = _
  rw [outer_graph_degree_eq, Equiv.apply_symm_apply]

/-- Forgetting the subtype of an induced copied edge preserves every subset degree. -/
theorem burning_degree_into_induced {N : ℕ} (V : Set (FiniteWired.Vertex N))
    (S : Finset V) (v : V) :
    Burning.degreeInto (inducedGraph V) S v =
      Burning.degreeInto (WiredTrees.graph N) (S.image Subtype.val) v.val := by
  unfold Burning.degreeInto Burning.incidentInto
  simp only [inducedGraph, Subtype.ext_iff, WiredTrees.graph,
    FiniteAvalanches.Trees.Multigraph.ofEndpoints]
  have hm : ∀ w : V, w ∈ S ↔ w.val ∈ S.image Subtype.val := by
    intro w
    constructor
    · exact Finset.mem_image_of_mem _
    · intro hw
      obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hw
      exact (Subtype.ext he : z = w) ▸ hz
  simp only [hm]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he
  · intro a _ b _ he
    exact Subtype.ext he
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hr
      refine ⟨⟨e, hl ▸ v.property, hew ▸ w.property⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        (Or.inl ⟨hl, Finset.mem_image.mpr ⟨w, hw, hew⟩⟩)
    · obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hl
      refine ⟨⟨e, hew ▸ w.property, hr ▸ v.property⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        (Or.inr ⟨hr, Finset.mem_image.mpr ⟨w, hw, hew⟩⟩)

end
end FiniteAvalanches.Sandpile.Components
