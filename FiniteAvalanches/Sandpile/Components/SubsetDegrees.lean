import FiniteAvalanches.Sandpile.Components.SourceDegrees

/-! Transport every tested subset through the literal site/vertex map. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Every finite subset degree at a member counts exactly its lattice neighbors.
The coordinate hypothesis states the literal map, not a supplied numerical identity. -/
theorem subset_site_degree {N : ℕ} {D : Finset Site2} (hD : D ⊆ boxSites N)
    (V : Set (FiniteWired.Vertex N)) (f : {x : Site2 // x ∈ D} → V)
    (hf : ∀ x, (f x).val = some (FiniteWired.activeOfSite N x.val
      ((mem_box_sites N _).mp (hD x.property))))
    (S : Finset {x : Site2 // x ∈ D}) (x : {x : Site2 // x ∈ D}) (hx : x ∈ S) :
    Burning.degreeInto (inducedGraph V) (S.image f) (f x) =
      degree (S.image Subtype.val) x.val := by
  let A := S.image Subtype.val
  have hA : A ⊆ boxSites N := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    exact hD z.property
  have hm : ∀ v : FiniteWired.Vertex N,
      v ∈ (S.image f).image Subtype.val ↔ insideVertex A v := by
    intro v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      rw [hf]
      exact Finset.mem_image_of_mem Subtype.val hz
    · cases v with
      | none => exact fun hv => hv.elim
      | some y =>
        intro hy
        obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hy
        refine Finset.mem_image.mpr ⟨f z, Finset.mem_image_of_mem f hz, ?_⟩
        rw [hf]
        apply congrArg some
        apply FiniteWired.site_injective N
        exact he
  let a := FiniteWired.activeOfSite N x.val ((mem_box_sites N _).mp (hD x.property))
  have hxa : insideVertex A (some a) := Finset.mem_image_of_mem Subtype.val hx
  have hi : Burning.incidentInto (WiredTrees.graph N)
      ((S.image f).image Subtype.val) (some a) =
        inducedIncidentCopies {v | insideVertex A v} a := by
    ext e
    simp only [Burning.incidentInto, inducedIncidentCopies, incident,
      Finset.mem_filter, Finset.mem_univ, true_and, WiredTrees.graph,
      FiniteAvalanches.Trees.Multigraph.ofEndpoints, Set.mem_setOf_eq, hm]
    constructor
    · rintro (⟨hl, hr⟩ | ⟨hr, hl⟩)
      · exact ⟨Or.inl hl, hl ▸ hxa, hr⟩
      · exact ⟨Or.inr hr, hl, hr ▸ hxa⟩
    · rintro ⟨hl | hr, ha, hb⟩
      · exact Or.inl ⟨hl, hb⟩
      · exact Or.inr ⟨hr, ha⟩
  rw [burning_degree_into_induced, hf]
  change Burning.degreeInto (WiredTrees.graph N) _ (some a) = _
  unfold Burning.degreeInto
  rw [hi]
  exact internal_copy_degree hA a (Finset.mem_image_of_mem Subtype.val hx)

theorem inner_subset_degree {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (S : Finset {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)})
    (x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)}) (hx : x ∈ S) :
    Burning.activeDegree (inducedGraph (insideSupport C))
      (Finset.univ.erase (innerRoot C)) (S.image (innerSourceVertexEquiv C))
        (innerSourceVertexEquiv C x) = degree (S.image Subtype.val) x.val := by
  unfold Burning.activeDegree
  rw [Finset.image_image]
  exact subset_site_degree ((Finset.erase_subset _ _).trans C.property.1)
    (insideSupport C) (fun z => (innerSourceVertexEquiv C z).val) (fun _ => rfl) S x hx

theorem outer_subset_degree {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (S : Finset {x : Site2 // x ∈ boxSites N \ C.val})
    (x : {x : Site2 // x ∈ boxSites N \ C.val}) (hx : x ∈ S) :
    Burning.activeDegree (inducedGraph (outsideSupport C))
      (Finset.univ.erase (outerRoot C)) (S.image (outerSourceVertexEquiv C))
        (outerSourceVertexEquiv C x) = degree (S.image Subtype.val) x.val := by
  unfold Burning.activeDegree
  rw [Finset.image_image]
  exact subset_site_degree Finset.sdiff_subset
    (outsideSupport C) (fun z => (outerSourceVertexEquiv C z).val) (fun _ => rfl) S x hx

end
end FiniteAvalanches.Sandpile.Components
