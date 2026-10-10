import FiniteAvalanches.Wilson.Branches

/-! Successful spanning queries from one root yield an actual copied spanning
tree. This is structural correctness, with no distributional identification. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open Quiver FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E I : Type} [Fintype V] [Fintype E] (G : Multigraph V E) (ι : E ↪ I)

theorem walk_vertex_has_time (x : V) (ω : Driver G) (n : ℕ) (v : ULift.{0} V)
    (hv : v ∈ @Path.vertices _ (pathQuiver G) _ _ (walkPath G x ω n)) :
    ∃ k ≤ n, position G x ω k = v.down := by
  letI := pathQuiver G
  induction n with
  | zero =>
    have he : v = ULift.up x := by simpa [walkPath, Path.vertices] using hv
    exact ⟨0, Nat.le_refl 0, congrArg ULift.down he.symm⟩
  | succ n ih =>
    rcases (Path.mem_vertices_cons _ _).mp hv with hv | hv
    · obtain ⟨k, hk, he⟩ := ih hv
      exact ⟨k, hk.trans (Nat.le_succ n), he⟩
    · exact ⟨n + 1, Nat.le_refl _, congrArg ULift.down hv.symm⟩

theorem attach_is_tree (s : State (V := V) (E := E) (I := I)) (hs : G.is_tree s.roots s.edges)
    (x : V) (ω : Driver G) (h : hits G s.roots x ω) :
    G.is_tree (attachAt G ι s x ω (Nat.find h)).roots (attachAt G ι s x ω (Nat.find h)).edges := by
  letI := pathQuiver G
  apply is_tree_attach_path G _ (loopErase_vertices_nodup _) s.roots s.edges hs (Nat.find_spec h)
  intro v hv hvr
  obtain ⟨k, hk, he⟩ := walk_vertex_has_time G x ω (Nat.find h) v
    ((loopErase_vertices_sublist _).subset hv)
  have heq : k = Nat.find h := by
    by_contra hn
    exact Nat.find_min h (lt_of_le_of_ne hk hn) (he.symm ▸ hvr)
  apply ULift.ext_iff.mpr
  simpa only [heq] using he.symm

theorem query_is_tree (s t : State (V := V) (E := E) (I := I))
    (hs : G.is_tree s.roots s.edges) (x : V) (ω : Driver G) (h : query G ι s x ω = some t) :
    G.is_tree t.roots t.edges := by
  unfold query at h
  split at h
  · cases h; exact hs
  · split at h
    · cases h; exact attach_is_tree G ι s hs x ω ‹_›
    · cases h

theorem query_roots_mono (s t : State (V := V) (E := E) (I := I)) (x : V) (ω : Driver G)
    (h : query G ι s x ω = some t) : s.roots ⊆ t.roots := by
  unfold query at h
  split at h
  · cases h; exact Set.Subset.refl _
  · split at h
    · cases h; exact Set.subset_union_left
    · cases h

theorem query_start_mem (s t : State (V := V) (E := E) (I := I)) (x : V) (ω : Driver G)
    (h : query G ι s x ω = some t) : x ∈ t.roots := by
  letI := pathQuiver G
  unfold query at h
  split at h
  · cases h; assumption
  · split at h
    · cases h; exact Or.inr (Path.start_mem_vertices _)
    · cases h

theorem explore_is_tree (s t : State (V := V) (E := E) (I := I)) (hs : G.is_tree s.roots s.edges)
    (order : List V) (ω : ℕ → Driver G) (h : explore G ι s order ω = some t) : G.is_tree t.roots t.edges := by
  induction order generalizing s ω with
  | nil => cases h; exact hs
  | cons x xs ih =>
    simp only [explore] at h
    cases he : query G ι s x (ω 0) with
    | none => simp only [he, Option.bind_none] at h; cases h
    | some u =>
      simp only [he, Option.bind_some] at h
      exact ih u (query_is_tree G ι s u hs x (ω 0) he) _ h

theorem explore_covers (s t : State (V := V) (E := E) (I := I)) (order : List V) (ω : ℕ → Driver G)
    (h : explore G ι s order ω = some t) : s.roots ⊆ t.roots ∧ ∀ v ∈ order, v ∈ t.roots := by
  induction order generalizing s ω with
  | nil => cases h; exact ⟨Set.Subset.refl _, by simp⟩
  | cons x xs ih =>
    simp only [explore] at h
    cases he : query G ι s x (ω 0) with
    | none => simp only [he, Option.bind_none] at h; cases h
    | some u =>
      simp only [he, Option.bind_some] at h
      obtain ⟨hmono, hxs⟩ := ih u _ h
      refine ⟨(query_roots_mono G ι s u x (ω 0) he).trans hmono, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with hvx | hv
      · subst v
        exact hmono (query_start_mem G ι s u x (ω 0) he)
      · exact hxs v hv

/-- An arbitrary spanning order, including skips and repetitions, yields a genuine
canonical copied tree on success. No random-walk or tree-law conclusion is a premise. -/
theorem spanning_output_is_tree (r : V) (order : List V) (horder : ∀ v, v = r ∨ v ∈ order)
    (ω : ℕ → Driver G) (t : State (V := V) (E := E) (I := I))
    (h : explore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω = some t) :
    t.roots = Set.univ ∧ G.is_tree Set.univ t.edges := by
  have hs : G.is_tree (initialState (E := E) (I := I) ⟨{r}, Set.singleton_nonempty r⟩).roots
      (initialState (E := E) (I := I) ⟨{r}, Set.singleton_nonempty r⟩).edges := G.is_tree_singleton_empty r
  obtain ⟨hm, hc⟩ := explore_covers G ι _ t order ω h
  have hr : t.roots = Set.univ := Set.eq_univ_of_forall (fun v => by
    rcases horder v with rfl | hv
    · exact hm (by simp [initialState])
    · exact hc v hv)
  refine ⟨hr, ?_⟩
  have ht := explore_is_tree G ι _ t hs order ω h
  rwa [hr] at ht

theorem single_vertex_empty_tree [Subsingleton V] (r : V) :
    G.is_tree Set.univ (∅ : Finset E) := by
  have he : ({r} : Set V) = Set.univ := Set.eq_univ_of_forall (fun v => Subsingleton.elim v r)
  simpa only [he] using G.is_tree_singleton_empty r

end
end FiniteAvalanches.Wilson.CopiedNetwork
