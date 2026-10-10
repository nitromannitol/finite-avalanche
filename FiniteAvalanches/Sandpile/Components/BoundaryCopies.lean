import FiniteAvalanches.Sandpile.Components.WiredTrees

/-! Boundary contacts count the original wired copies at every inside vertex. -/
namespace FiniteAvalanches.Sandpile.Components
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open scoped Classical
noncomputable section

theorem induced_degree_eq_degree_into {N : ℕ} (D : Set (FiniteWired.Vertex N)) (v : D) :
    Burning.degree (inducedGraph D) v =
      Burning.degreeInto (WiredTrees.graph N) D.toFinset v.val := by
  unfold Burning.degree
  rw [burning_degree_into_induced]
  congr 1
  ext w
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_toFinset]
  constructor
  · rintro ⟨x, rfl⟩
    exact x.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

theorem crossing_at_eq_incident_into_complement {N : ℕ}
    (D : Set (FiniteWired.Vertex N)) (v : D) :
    (WiredTrees.graph N).crossingAt D v.val =
      Burning.incidentInto (WiredTrees.graph N) (Finset.univ \ D.toFinset) v.val := by
  ext e
  simp only [Multigraph.crossingAt, Burning.incidentInto, Finset.mem_filter,
    Finset.mem_univ, true_and, v.property, Finset.mem_sdiff, Set.mem_toFinset]

theorem crossing_card_add_induced_degree {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (v : insideSupport C) :
    ((WiredTrees.graph N).crossingAt (insideSupport C) v.val).card +
      Burning.degree (inducedGraph (insideSupport C)) v = 4 := by
  rw [crossing_at_eq_incident_into_complement, induced_degree_eq_degree_into]
  change Burning.degreeInto (WiredTrees.graph N)
      (Finset.univ \ (insideSupport C).toFinset) v.val +
    Burning.degreeInto (WiredTrees.graph N) (insideSupport C).toFinset v.val = 4
  rw [Burning.degree_into_compl]
  rcases v with ⟨_ | x, hv⟩
  · exact hv.elim
  · exact wired_graph_degree x

theorem crossing_card_eq_four_sub_degree {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (v : insideSupport C) :
    ((WiredTrees.graph N).crossingAt (insideSupport C) v.val).card =
      4 - Burning.degree (inducedGraph (insideSupport C)) v := by
  have h := crossing_card_add_induced_degree C v
  omega

theorem crossing_nonempty_iff_degree_lt_four {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (v : insideSupport C) :
    ((WiredTrees.graph N).crossingAt (insideSupport C) v.val).Nonempty ↔
      Burning.degree (inducedGraph (insideSupport C)) v < 4 := by
  rw [← Finset.card_pos, crossing_card_eq_four_sub_degree]
  omega

theorem admissible_nonempty_iff_degree_contact {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (K : Set (FiniteWired.Vertex N)) (hK : K ⊆ insideSupport C) :
    ((WiredTrees.graph N).admissibleEdges (insideSupport C) K).Nonempty ↔
      ∃ v : insideSupport C, Burning.degree (inducedGraph (insideSupport C)) v < 4 ∧
        v.val ∈ K := by
  rw [Multigraph.admissibleEdges_eq_biUnion, Finset.biUnion_nonempty]
  constructor
  · rintro ⟨v, hv, hc⟩
    have hvK := Set.mem_toFinset.mp hv
    exact ⟨⟨v, hK hvK⟩, (crossing_nonempty_iff_degree_lt_four C ⟨v, hK hvK⟩).mp hc, hvK⟩
  · rintro ⟨v, hd, hv⟩
    exact ⟨v.val, Set.mem_toFinset.mpr hv, (crossing_nonempty_iff_degree_lt_four C v).mpr hd⟩

end
end FiniteAvalanches.Sandpile.Components
