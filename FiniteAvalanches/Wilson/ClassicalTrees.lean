import FiniteAvalanches.Wilson.ClassicalProtocol
import FiniteAvalanches.Wilson.SpanningTrees

/-! Successful outputs of the actual first-unretained copied protocol are
genuine trees. A tree is constructed only from a successful spanning run. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E I : Type} [Fintype V] [Fintype E]
variable (G : Multigraph V E) (ι : E ↪ I)

theorem classicalExplore_is_tree (s t : State (V := V) (E := E) (I := I))
    (hs : G.is_tree s.roots s.edges) (order : List V) (ω : ℕ → Driver G)
    (h : classicalExplore G ι s order ω = some t) : G.is_tree t.roots t.edges := by
  induction order generalizing s ω with
  | nil => cases h; exact hs
  | cons x xs ih =>
    by_cases hx : x ∈ s.roots
    · simp only [classicalExplore, if_pos hx] at h
      exact ih s hs ω h
    · simp only [classicalExplore, if_neg hx] at h
      cases he : query G ι s x (ω 0) with
      | none => simp only [he, Option.bind_none] at h; cases h
      | some u =>
        simp only [he, Option.bind_some] at h
        exact ih u (query_is_tree G ι s u hs x (ω 0) he) _ h

theorem classicalExplore_covers (s t : State (V := V) (E := E) (I := I))
    (order : List V) (ω : ℕ → Driver G) (h : classicalExplore G ι s order ω = some t) :
    s.roots ⊆ t.roots ∧ ∀ v ∈ order, v ∈ t.roots := by
  induction order generalizing s ω with
  | nil => cases h; exact ⟨Set.Subset.refl _, by simp⟩
  | cons x xs ih =>
    by_cases hx : x ∈ s.roots
    · simp only [classicalExplore, if_pos hx] at h
      obtain ⟨hm, hc⟩ := ih s ω h
      refine ⟨hm, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hm hx
      · exact hc v hv
    · simp only [classicalExplore, if_neg hx] at h
      cases he : query G ι s x (ω 0) with
      | none => simp only [he, Option.bind_none] at h; cases h
      | some u =>
        simp only [he, Option.bind_some] at h
        obtain ⟨hm, hc⟩ := ih u _ h
        refine ⟨(query_roots_mono G ι s u x (ω 0) he).trans hm, ?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with hvx | hv
        · subst v
          exact hm (query_start_mem G ι s u x (ω 0) he)
        · exact hc v hv

theorem classical_spanning_output_is_tree (r : V) (order : List V)
    (horder : ∀ v, v = r ∨ v ∈ order) (ω : ℕ → Driver G)
    (t : State (V := V) (E := E) (I := I))
    (h : classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω = some t) :
    t.roots = Set.univ ∧ G.is_tree Set.univ t.edges := by
  obtain ⟨hm, hc⟩ := classicalExplore_covers G ι _ t order ω h
  have hr : t.roots = Set.univ := Set.eq_univ_of_forall (fun v => by
    rcases horder v with rfl | hv
    · exact hm (by simp [initialState])
    · exact hc v hv)
  refine ⟨hr, ?_⟩
  have ht := classicalExplore_is_tree G ι _ t (G.is_tree_singleton_empty r) order ω h
  rwa [hr] at ht

def classicalTreeAtSuccess (r : V) (order : List V) (horder : ∀ v, v = r ∨ v ∈ order)
    (ω : ℕ → Driver G) (t : State (V := V) (E := E) (I := I))
    (h : classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω = some t) :
    G.ComponentTree Set.univ := ⟨t.edges, (classical_spanning_output_is_tree G ι r order horder ω t h).2⟩

end
end FiniteAvalanches.Wilson.CopiedNetwork
