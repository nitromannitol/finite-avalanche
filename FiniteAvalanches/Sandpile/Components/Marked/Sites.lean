import FiniteAvalanches.Sandpile.Components.HeldBoundary
import FiniteAvalanches.Trees.MarkedPast
import FiniteAvalanches.Sandpile.Burning.PastAdapter

/-! Literal marked sites and rooted past contact in an induced source component.
The root is retained in the full marked carrier and excluded only from held vertices. -/
namespace FiniteAvalanches.Sandpile.Components.Marked
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Original lattice coordinate of every vertex of the inside induced graph. -/
def insideSite {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (v : insideSupport C) : Site2 := (insideVertexEquiv C v).val

/-- Literal preimage of a lattice marked set on the entire induced vertex carrier. -/
def markedVertices {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (S : Finset Site2) : Finset (insideSupport C) := Finset.univ.filter fun v => insideSite C v ∈ S

theorem mem_marked_vertices {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (S : Finset Site2) (v : insideSupport C) : v ∈ markedVertices C S ↔ insideSite C v ∈ S := by
  simp [markedVertices]

theorem inside_site_root {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    insideSite C (innerRoot C) = FiniteWired.site o := rfl

theorem marked_root_mem {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (S : Finset Site2) (ho : FiniteWired.site o ∈ S) : innerRoot C ∈ markedVertices C S := by
  rw [mem_marked_vertices, inside_site_root]
  exact ho

theorem inside_site_inner {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (v : Burning.SourceVertex (innerRoot C)) : insideSite C v.val = innerSite C v := by
  let x := (innerSourceVertexEquiv C).symm v
  have he : innerSourceVertexEquiv C x = v := (innerSourceVertexEquiv C).apply_symm_apply v
  rw [← he]
  change (insideVertexEquiv C ((innerVertexEquiv C).symm x).val).val = _
  have hh := congrArg Subtype.val ((innerVertexEquiv C).apply_symm_apply x)
  exact hh

theorem inside_site_injective {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Function.Injective (insideSite C) := fun _ _ h => (insideVertexEquiv C).injective (Subtype.ext h)

theorem marked_sites_image {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (S : Finset Site2) (hS : S ⊆ C.val) : (markedVertices C S).image (insideSite C) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_marked_vertices C S v).mp hv
  · intro hx
    let v := (insideVertexEquiv C).symm ⟨x, hS hx⟩
    have he : insideSite C v = x := congrArg Subtype.val ((insideVertexEquiv C).apply_symm_apply ⟨x, hS hx⟩)
    exact Finset.mem_image.mpr ⟨v, (mem_marked_vertices C S v).mpr (he ▸ hx), he⟩

theorem inside_sites_of_source_set {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (T : Finset (Burning.SourceVertex (innerRoot C))) :
    (T.image Subtype.val).image (insideSite C) = T.image (innerSite C) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro v _
  exact inside_site_inner C v

theorem marked_omitted_iff_stop_meets {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (h : CoreField o C.val) (S : Finset Site2) (hS : S ⊆ C.val) :
    (¬ S ⊆ heldInterior h.val.val C) ↔
      ∃ v ∈ markedVertices C S,
        v ∈ (Burning.heldBurning (inducedGraph (insideSupport C)) (Finset.univ.erase (innerRoot C))
          (coreGraphFieldEquiv C h).2.val (boundaryVertices C)).image Subtype.val := by
  rw [held_interior_eq_canonical_complement C h]
  constructor
  · intro hn
    obtain ⟨x, hx, hxb⟩ := Finset.not_subset.mp hn
    have hm : x ∈ (Burning.heldBurning (inducedGraph (insideSupport C))
      (Finset.univ.erase (innerRoot C)) (coreGraphFieldEquiv C h).2.val (boundaryVertices C)).image (innerSite C) := by
      by_contra hm
      exact hxb (Finset.mem_sdiff.mpr ⟨hS hx, hm⟩)
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
    refine ⟨v.val, (mem_marked_vertices C S v.val).mpr ?_, Finset.mem_image_of_mem _ hv⟩
    rw [inside_site_inner C v, he]
    exact hx
  · rintro ⟨v, hvS, hv⟩
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    intro hh
    have hx := hh ((mem_marked_vertices C S w.val).mp hvS)
    rw [inside_site_inner C w] at hx
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_image_of_mem _ hw)

theorem past_meets_marked_iff_boundary_span {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (S : Finset Site2) (ho : FiniteWired.site o ∈ S) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    ∀ t : (inducedGraph (insideSupport C)).SpanningTree, (∃ v ∈ markedVertices C S, v ∈ Burning.canonicalPastUnion
      (inducedGraph (insideSupport C)) (innerRoot C) t (boundaryVertices C)) ↔
    ∃ b ∈ boundaryVertices C, b.val ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S) := by
  letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
  intro t
  have he := (inducedGraph (insideSupport C)).past_union_meets_iff_span t (innerRoot C)
    (markedVertices C S : Set (insideSupport C)) (marked_root_mem C S ho)
    ((boundaryVertices C).image (sourceVertexEquiv (innerRoot C)) : Set {v : insideSupport C // v ≠ innerRoot C})
  constructor
  · rintro ⟨v, hvS, hv⟩
    obtain ⟨_, b, hb, hvb⟩ := Finset.mem_filter.mp hv
    have hleft := he.mp ⟨v, hvS, sourceVertexEquiv (innerRoot C) b, Finset.mem_image_of_mem _ hb, hvb⟩
    obtain ⟨b, hb, hspan⟩ := hleft
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨w, hw, hspan⟩
  · rintro ⟨b, hb, hspan⟩
    obtain ⟨v, hv, w, hw, hmem⟩ := he.mpr
      ⟨sourceVertexEquiv (innerRoot C) b, Finset.mem_image_of_mem _ hb, hspan⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨v, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, hmem⟩⟩


end
end FiniteAvalanches.Sandpile.Components.Marked
