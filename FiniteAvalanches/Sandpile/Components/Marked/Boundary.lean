import FiniteAvalanches.Sandpile.Components.Marked.Sites

/-! The paper's N[o] ⊆ S ⊆ C proves that the root is interior. Therefore
removing the source from the held boundary loses no actual boundary vertex. -/
namespace FiniteAvalanches.Sandpile.Components.Marked
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

theorem source_degree_four_of_marked_neighbors {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (S : Finset Site2) (hS : S ⊆ C.val)
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    degree C.val (FiniteWired.site o) = 4 := by
  have hp (i : Fin 2) : FiniteWired.site o + unit i ∈ C.val :=
    hS (hN (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_insert_self _ _⟩)))
  have hm (i : Fin 2) : FiniteWired.site o - unit i ∈ C.val :=
    hS (hN (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)))
  have he := degree_eq_sum C.val (FiniteWired.site o)
  simp only [nbrSumZ, Fin.sum_univ_two, if_pos (hp 0), if_pos (hp 1),
    if_pos (hm 0), if_pos (hm 1)] at he
  omega

theorem marked_root_degree_four {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (S : Finset Site2) (hS : S ⊆ C.val)
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    Burning.degree (inducedGraph (insideSupport C)) (innerRoot C) = 4 := by
  rw [burning_degree_eq, inner_graph_degree_eq]
  exact source_degree_four_of_marked_neighbors C S hS hN

/-- Every full induced vertex with deficient copied degree is held; the root
exclusion follows from its proved degree four, not a supplied paper premise. -/
theorem marked_full_boundary_vertices {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (S : Finset Site2) (hS : S ⊆ C.val)
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    (boundaryVertices C).image Subtype.val =
      Finset.univ.filter (fun v : insideSupport C => Burning.degree
        (inducedGraph (insideSupport C)) v < 4) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_boundary_vertices_degree C w).mp hw
  · intro hv
    have hn : v ≠ innerRoot C := by
      intro he
      rw [he, marked_root_degree_four C S hS hN] at hv
      omega
    let w : Burning.SourceVertex (innerRoot C) :=
      (sourceVertexEquiv (innerRoot C)).symm ⟨v, hn⟩
    have he : w.val = v := rfl
    refine ⟨w, (mem_boundary_vertices_degree C w).mpr ?_, he⟩
    rw [he]
    exact hv

/-- Boundary contact can be tested on the entire induced vertex carrier. -/
theorem marked_boundary_contact_iff {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (S : Finset Site2) (hS : S ⊆ C.val)
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    ∀ t : (inducedGraph (insideSupport C)).SpanningTree,
      (∃ b ∈ boundaryVertices C,
        b.val ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)) ↔
      ∃ v : insideSupport C, Burning.degree (inducedGraph (insideSupport C)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S) := by
  letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
  intro t
  constructor
  · rintro ⟨b, hb, hspan⟩
    exact ⟨b.val, (mem_boundary_vertices_degree C b).mp hb, hspan⟩
  · rintro ⟨v, hv, hspan⟩
    have hm : v ∈ (boundaryVertices C).image Subtype.val := by
      rw [marked_full_boundary_vertices C S hS hN]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨b, hb, hspan⟩

end
end FiniteAvalanches.Sandpile.Components.Marked
