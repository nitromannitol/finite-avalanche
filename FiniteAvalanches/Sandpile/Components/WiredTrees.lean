import FiniteAvalanches.Sandpile.Components.SourceDegrees
import FiniteAvalanches.Sandpile.Burning.CanonicalEquiv
import FiniteAvalanches.Sandpile.Components.Directions

/-! The original Recurrent carrier is literal noForbidden on the actual wired
copied graph with sink none. Its normalization is identified by a proved Equiv,
without importing any Markov recurrence characterization. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves ComponentTransport
open scoped Classical
noncomputable section

def wiredSourceVertexEquiv (N : ℕ) :
    FiniteWired.Active N ≃ Burning.SourceVertex (none : FiniteWired.Vertex N) where
  toFun x := ⟨some x, by simp⟩
  invFun v := match v with
    | ⟨none, hv⟩ => ((Finset.mem_erase.mp hv).1 rfl).elim
    | ⟨some x, _⟩ => x
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨_ | x, hv⟩
    · exact ((Finset.mem_erase.mp hv).1 rfl).elim
    · rfl

theorem wired_graph_degree {N : ℕ} (x : FiniteWired.Active N) :
    Burning.degree (WiredTrees.graph N) (some x) = 4 := by
  have he : Burning.incidentInto (WiredTrees.graph N) Finset.univ (some x) =
      (Finset.univ : Finset FiniteWired.Direction).image (FiniteWired.directionEdge x) := by
    ext e
    simp only [Burning.incidentInto, WiredTrees.graph,
      FiniteAvalanches.Trees.Multigraph.ofEndpoints, Finset.mem_filter,
      Finset.mem_univ, and_true, true_and, Finset.mem_image]
    constructor
    · exact exists_direction_of_incident x e
    · rintro ⟨d, _, rfl⟩
      exact direction_edge_incident x d
  unfold Burning.degree Burning.degreeInto
  rw [he, Finset.card_image_of_injective _ (direction_edge_injective x)]
  decide

theorem wired_subset_degree {N : ℕ} (S : Finset (FiniteWired.Active N))
    (x : FiniteWired.Active N) (hx : x ∈ S) :
    Burning.activeDegree (WiredTrees.graph N) (Finset.univ.erase none)
      (S.image (wiredSourceVertexEquiv N)) (wiredSourceVertexEquiv N x) =
        FiniteWired.internalDegree S x := by
  let A := S.image FiniteWired.site
  have hm : ∀ v : FiniteWired.Vertex N,
      v ∈ S.image some ↔ insideVertex A v := by
    intro v
    cases v with
    | none => simp [insideVertex]
    | some y =>
      constructor
      · intro hy
        obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hy
        have hz' : z = y := Option.some.inj he
        subst z
        exact Finset.mem_image_of_mem FiniteWired.site hz
      · intro hy
        obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hy
        exact Finset.mem_image.mpr ⟨z, hz, congrArg some (FiniteWired.site_injective N he)⟩
  have hxa : insideVertex A (some x) := Finset.mem_image_of_mem FiniteWired.site hx
  have hi : Burning.incidentInto (WiredTrees.graph N) (S.image some) (some x) =
      inducedIncidentCopies {v | insideVertex A v} x := by
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
  unfold Burning.activeDegree
  rw [Finset.image_image]
  change Burning.degreeInto (WiredTrees.graph N) (S.image some) (some x) = _
  unfold Burning.degreeInto
  rw [hi]
  have hA : A ⊆ boxSites N := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    exact site_mem_box z
  exact internal_copy_degree hA x hxa

def wiredSourceHeightsEquiv (N : ℕ) :
    FiniteWired.Heights N ≃ Burning.SourceHeights (WiredTrees.graph N) none :=
  reindexHeights (wiredSourceVertexEquiv N) (fun _ => 4)
    (fun v => Burning.degree (WiredTrees.graph N) v.val) wired_graph_degree

theorem original_recurrent_iff (N : ℕ) (h : FiniteWired.Heights N) :
    FiniteWired.recurrent h ↔ Burning.noForbidden (WiredTrees.graph N)
      (Finset.univ.erase none) (wiredSourceHeightsEquiv N h) :=
  indexed_allowed_iff (wiredSourceVertexEquiv N) (fun _ => 4)
    (fun v => Burning.degree (WiredTrees.graph N) v.val) wired_graph_degree
    FiniteWired.internalDegree (Burning.activeDegree (WiredTrees.graph N) (Finset.univ.erase none))
    wired_subset_degree h

def originalRecurrentGraphEquiv (N : ℕ) :
    FiniteWired.Recurrent N ≃ {h : Burning.SourceHeights (WiredTrees.graph N) none //
      Burning.noForbidden (WiredTrees.graph N) (Finset.univ.erase none) h} :=
  Equiv.subtypeEquiv (wiredSourceHeightsEquiv N) (original_recurrent_iff N)

def originalRecurrentTreeEquiv (N : ℕ) :
    FiniteWired.Recurrent N ≃ (WiredTrees.graph N).SpanningTree := by
  letI : LinearOrder (FiniteWired.Edge N) := LinearOrder.lift' (Fintype.equivFin (FiniteWired.Edge N))
    (Fintype.equivFin (FiniteWired.Edge N)).injective
  exact (originalRecurrentGraphEquiv N).trans (Burning.canonicalBurningEquiv (dE := Classical.decEq _) (WiredTrees.graph N) none)

end
end FiniteAvalanches.Sandpile.Components
