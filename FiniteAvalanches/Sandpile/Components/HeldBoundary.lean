import FiniteAvalanches.Sandpile.Components.HeldStop

/-! Apply the exact stopping-set transport to the manuscript's actual nonsource
held boundary, and to the parent's entire burned set. No held-past law is used. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Every canonical nonsink boundary vertex, with its original copied degree. -/
def boundaryVertices {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Finset (Burning.SourceVertex (innerRoot C)) := innerVertices C (heldBoundary C)

theorem boundary_vertex_sites {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    (boundaryVertices C).image (innerSite C) = heldBoundary C :=
  image_inner_vertices C _ (Finset.filter_subset _ _)

theorem mem_boundary_vertices_degree {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (v : Burning.SourceVertex (innerRoot C)) :
    v ∈ boundaryVertices C ↔ Burning.degree (inducedGraph (insideSupport C)) v.val < 4 := by
  have hd := inner_source_degree C ((innerSourceVertexEquiv C).symm v)
  rw [Equiv.apply_symm_apply] at hd
  rw [hd]
  change v ∈ innerVertices C (heldBoundary C) ↔ degree C.val (innerSite C v) < 4
  rw [mem_inner_vertices]
  simp only [heldBoundary, Finset.mem_filter, inner_site_mem, true_and]

/-- Actual source-boundary held burns agree as complete lattice sets. -/
theorem core_boundary_stop_eq {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (h : CoreField o C.val) :
    (Burning.heldBurning (inducedGraph (insideSupport C)) (Finset.univ.erase (innerRoot C))
      (coreGraphFieldEquiv C h).2.val (boundaryVertices C)).image (innerSite C) =
    heldBurning (wiredHeight 4 h.val.val) (heldBoundary C)
      (C.val.erase (FiniteWired.site o)) (Finset.filter_subset _ _) := by
  have he := core_held_stop_eq C h (boundaryVertices C)
  simpa only [boundary_vertex_sites] using he

/-- The parent's actual burned set, including the source, in canonical graph notation. -/
theorem held_interior_eq_canonical_complement {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (h : CoreField o C.val) :
    heldInterior h.val.val C = C.val \
      (Burning.heldBurning (inducedGraph (insideSupport C)) (Finset.univ.erase (innerRoot C))
        (coreGraphFieldEquiv C h).2.val (boundaryVertices C)).image (innerSite C) := by
  rw [core_boundary_stop_eq]
  rfl

/-- All canonical stopping vertices belong to the literal held interior complement. -/
theorem every_stopping_vertex_outside_burned {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (h : CoreField o C.val)
    (v : Burning.SourceVertex (innerRoot C))
    (hv : v ∈ Burning.heldBurning (inducedGraph (insideSupport C))
      (Finset.univ.erase (innerRoot C)) (coreGraphFieldEquiv C h).2.val (boundaryVertices C)) :
    innerSite C v ∉ heldInterior h.val.val C := by
  rw [held_interior_eq_canonical_complement C h]
  intro hm
  exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_image_of_mem _ hv)

/-- The removed sink is actually burned; membership is derived from the shape. -/
theorem actual_source_burned {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (h : CoreField o C.val) :
    FiniteWired.site o ∈ heldInterior h.val.val C := by
  rw [held_interior_eq_canonical_complement C h]
  refine Finset.mem_sdiff.mpr ⟨C.property.2, ?_⟩
  intro hm
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
  exact (Finset.mem_erase.mp (inner_site_mem C v)).1 hv

end
end FiniteAvalanches.Sandpile.Components
