import FiniteAvalanches.Sandpile.Components.Marked.Sites
import FiniteAvalanches.Sandpile.Components.Supports
import FiniteAvalanches.Trees.InducedSpan

/-! The whole lattice marked carrier maps to the original copied graph without
losing the root. The parent's proved induced path transport gives its full span. -/
namespace FiniteAvalanches.Sandpile.Components.Marked
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem original_marked_preimage {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (S : Finset (FiniteWired.Active N)) :
    {v : insideSupport C | v.val ∈ Components.markedVertices S} =
      (markedVertices C (markedSites S) : Set (insideSupport C)) := by
  ext v
  rcases v with ⟨_ | x, hx⟩
  · exact hx.elim
  · change (∃ y ∈ S, some y = some x) ↔
      (⟨some x, hx⟩ : insideSupport C) ∈ markedVertices C (markedSites S)
    rw [mem_marked_vertices]
    change (∃ y ∈ S, some y = some x) ↔ FiniteWired.site x ∈ S.image FiniteWired.site
    constructor
    · rintro ⟨y, hy, he⟩
      exact Finset.mem_image.mpr ⟨y, hy, congrArg FiniteWired.site (Option.some.inj he)⟩
    · intro hm
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
      exact ⟨y, hy, congrArg some (FiniteWired.site_injective N he)⟩

theorem original_marked_image {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (S : Finset (FiniteWired.Active N))
    (hS : markedSites S ⊆ C.val) :
    Subtype.val '' (markedVertices C (markedSites S) : Set (insideSupport C)) =
      Components.markedVertices S := by
  rw [← original_marked_preimage]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    exact ⟨⟨v, (marked_subset_iff S C).mp hS hv⟩, hv, rfl⟩

/-- Actual original edge-subset component span, for every tree and marked vertex. -/
theorem original_marked_span {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (S : Finset (FiniteWired.Active N))
    (hS : markedSites S ⊆ C.val) (t : (inducedGraph (insideSupport C)).SpanningTree) :
    (WiredTrees.graph N).componentSpan (innerInducedTreeEquiv C t)
      (Components.markedVertices S) ((marked_subset_iff S C).mp hS) =
      Subtype.val '' (inducedGraph (insideSupport C)).span t
        (markedVertices C (markedSites S)) := by
  have he := (WiredTrees.graph N).componentSpan_eq_image_span (insideSupport C) t
    (Components.markedVertices S) ((marked_subset_iff S C).mp hS)
  rw [original_marked_preimage] at he
  exact he

end
end FiniteAvalanches.Sandpile.Components.Marked
