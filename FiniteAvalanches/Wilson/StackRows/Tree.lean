import FiniteAvalanches.Wilson.StackRows.Terminal

/-! Wilson's theorem for the classical protocol. On stacks whose cycle popping terminates,
every walk of the stack protocol attaches a loop-erased branch made of terminal arrows, so
the output edges are the copies of the terminal arrows at the nonroot vertices; their law
is uniform over spanning trees. By the comparison of protocols, the classical protocol
with a fresh row of independent uniform letters for every walk has the same tree law. The
recorded history uses an embedding of the copies, which affects neither success nor the
edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CopiedNetwork

open Quiver MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V E I : Type} [Fintype V] [Fintype E] (G : Multigraph V E) (ι : E ↪ I)

/-- The copies selected at the terminal cursor by the vertices of `S` outside `R0`. -/
def terminalCopies (σ : CopyStacks G) (t : Cursor V) (R0 S : Set V) : Finset E :=
  (Finset.univ.filter (fun v => v ∈ S ∧ v ∉ R0)).image (fun v => (σ (v, t v)).val)

/-- Along a terminating cycle popping, the stack protocol attaches only terminal arrows. -/
theorem stackRun_terminal (σ : CopyStacks G) (R0 : Set V) (t : Cursor V) (L : List V) :
    ∀ (s : State (V := V) (E := E) (I := I)) (k : Cursor V), R0 ⊆ s.roots →
      Relation.ReflTransGen (pop_step s.roots (incidentCopyHead G) (fun v i => σ (v, i))) k t →
      terminal s.roots (incidentCopyHead G) (fun v i => σ (v, i)) t →
      s.edges = terminalCopies G σ t R0 s.roots →
      ∃ s', stackRun G ι σ s k L = some s' ∧ s.roots ⊆ s'.roots ∧ (∀ v ∈ L, v ∈ s'.roots) ∧
        s'.edges = terminalCopies G σ t R0 s'.roots := by
  induction L with
  | nil =>
    intro s k _ _ _ he
    exact ⟨s, rfl, subset_rfl, by simp, he⟩
  | cons x xs ih =>
    intro s k hR0 hrun ht he
    by_cases hx : x ∈ s.roots
    · obtain ⟨s', hs', hsub, hcov, he'⟩ := ih s k hR0 hrun ht he
      refine ⟨s', by simp only [stackRun, if_pos hx]; exact hs', hsub, ?_, he'⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hsub hx
      · exact hcov v hv
    · letI : Quiver V := instructionQuiver (incidentCopyHead G)
      obtain ⟨n, hn, hfirst, _, _, hcont, hterm⟩ := terminal_after_firstHit_branch s.roots
        (incidentCopyHead G) (fun v i => σ (v, i)) k t hrun ht x
      obtain ⟨n', hn', hfirst', hsel⟩ := terminal_selects_firstHit_erasure s.roots
        (incidentCopyHead G) (fun v i => σ (v, i)) k t hrun ht x
      have hnn : n' = n := by
        rcases lt_trichotomy n' n with h | h | h
        · exact absurd hn' (hfirst n' h)
        · exact h
        · exact absurd hn (hfirst' n h)
      subst hnn
      have hq := query_stackDriver_of_hit G ι s σ k x hx n' hn' hfirst'
      have hc := stackCursor_of_hit G σ s.roots k x n' hn' hfirst'
      have hroots := attachAt_stackDriver_roots G ι s σ k x n'
      have hedges := attachAt_stackDriver_edges G ι s σ k x n'
      have hcop := pathCopies_mapPath_of_selected G σ t (loopErase (stackTrace G σ k x n').2) hsel
      have hdep : ∀ v ∈ departures (loopErase (stackTrace G σ k x n').2), v ∉ s.roots :=
        fun v hv => instructionTrace_departures_avoid s.roots (incidentCopyHead G)
          (fun v i => σ (v, i)) k x n' hfirst' v (departures_loopErase_subset _ v hv)
      have hvert : ∀ v ∈ (loopErase (stackTrace G σ k x n').2).vertices, v ∉ s.roots →
          v ∈ departures (loopErase (stackTrace G σ k x n').2) := by
        intro v hv hvs
        rw [← Path.dropLast_append_end_eq (loopErase (stackTrace G σ k x n').2)] at hv
        rcases List.mem_append.mp hv with h | h
        · exact h
        · exact absurd ((List.mem_singleton.mp h) ▸ hn') hvs
      let s1 := attachAt G ι s x (stackDriver G σ k x) n'
      have hsub1 : s.roots ⊆ s1.roots := by
        change s.roots ⊆ (attachAt G ι s x (stackDriver G σ k x) n').roots
        rw [hroots]
        exact Set.subset_union_left
      have he1 : s1.edges = terminalCopies G σ t R0 s1.roots := by
        change (attachAt G ι s x (stackDriver G σ k x) n').edges =
          terminalCopies G σ t R0 (attachAt G ι s x (stackDriver G σ k x) n').roots
        rw [hedges, hcop, he, hroots]
        ext e
        simp only [terminalCopies, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map, Set.mem_union,
          Set.mem_setOf_eq]
        constructor
        · rintro (⟨v, ⟨h1, h2⟩, rfl⟩ | ⟨v, hv, rfl⟩)
          · exact ⟨v, ⟨Or.inl h1, h2⟩, rfl⟩
          · exact ⟨v, ⟨Or.inr (List.mem_of_mem_dropLast hv), fun h => hdep v hv (hR0 h)⟩, rfl⟩
        · rintro ⟨v, ⟨h1 | h1, h2⟩, rfl⟩
          · exact Or.inl ⟨v, ⟨h1, h2⟩, rfl⟩
          · by_cases hvs : v ∈ s.roots
            · exact Or.inl ⟨v, ⟨hvs, h2⟩, rfl⟩
            · exact Or.inr ⟨v, hvert v h1 hvs, rfl⟩
      have hcont1 : Relation.ReflTransGen (pop_step s1.roots (incidentCopyHead G)
          (fun v i => σ (v, i))) (erasedCursor k (stackTrace G σ k x n').2) t := by
        change Relation.ReflTransGen (pop_step (attachAt G ι s x (stackDriver G σ k x) n').roots
          (incidentCopyHead G) (fun v i => σ (v, i))) _ t
        rw [hroots]
        exact hcont
      have hterm1 : terminal s1.roots (incidentCopyHead G) (fun v i => σ (v, i)) t := by
        change terminal (attachAt G ι s x (stackDriver G σ k x) n').roots _ _ t
        rw [hroots]
        exact hterm
      obtain ⟨s', hs', hsub, hcov, he'⟩ :=
        ih s1 (erasedCursor k (stackTrace G σ k x n').2) (hR0.trans hsub1) hcont1 hterm1 he1
      refine ⟨s', ?_, hsub1.trans hsub, ?_, he'⟩
      · simp only [stackRun, if_neg hx]
        rw [hq, Option.bind_some, hc]
        exact hs'
      · intro v hv
        rcases List.mem_cons.mp hv with hvx | hv
        · apply hsub
          change v ∈ (attachAt G ι s x (stackDriver G σ k x) n').roots
          rw [hroots, hvx]
          exact Or.inr (Path.start_mem_vertices _)
        · exact hcov v hv

variable [Nontrivial V] (hconn : ∀ x y, G.reaches Finset.univ x y)
variable [∀ v, Nonempty (IncidentCopy G v)]

include hconn in
/-- The stack protocol from one root samples the uniform spanning tree of copies. -/
theorem variableStackLaw_stackRun_tree (r : V) (order : List V) (hspan : ∀ v, v ≠ r → v ∈ order)
    (k : Cursor V) (T : G.SpanningTree) :
    variableStackLaw (IncidentCopy G) {σ | ∃ s, stackRun G ι σ
        (initialState ⟨{r}, Set.singleton_nonempty r⟩) k order = some s ∧ s.edges = T.val} =
      (Fintype.card G.SpanningTree : ℝ≥0∞)⁻¹ := by
  let s₀ : State (V := V) (E := E) (I := I) := initialState ⟨{r}, Set.singleton_nonempty r⟩
  let a₀ : GoodIncidentArrows G {r} := forestIncidentArrows G {r}
    ((singletonRootedForestEquiv G r).symm (Classical.choice (G.nonempty_spanning_tree hconn)))
  have hae := variableStackLaw_ae_terminates (IncidentCopy G) {r} (incidentCopyHead G) k a₀
  have hlaw := variableStackLaw_spanningTreeEvent_eq G r k {T}
  rw [Nat.card_unique, Nat.cast_one, one_div] at hlaw
  rw [← hlaw]
  apply measure_congr
  filter_upwards [hae] with σ hσ
  obtain ⟨t, hrun, ht⟩ := hσ
  obtain ⟨s', hs', hsub, hcov, he'⟩ := stackRun_terminal G ι σ {r} t order s₀ k subset_rfl hrun ht
    (by
      show (∅ : Finset E) = terminalCopies G σ t {r} {r}
      symm
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      obtain ⟨v, hv, _⟩ := Finset.mem_image.mp he
      have hv' := (Finset.mem_filter.mp hv).2
      exact hv'.2 hv'.1)
  have huniv : ∀ v, v ∈ s'.roots := by
    intro v
    by_cases hv : v = r
    · exact hsub (hv ▸ Set.mem_singleton r)
    · exact hcov v (hspan v hv)
  let a : GoodIncidentArrows G {r} := ⟨fun v => σ (v, t v), ht⟩
  have hedges : s'.edges = incidentArrowCopies G {r} a := by
    rw [he']
    ext e
    simp only [terminalCopies, incidentArrowCopies, rootwardCopies, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, huniv, a]
  apply propext
  change (∃ s, stackRun G ι σ s₀ k order = some s ∧ s.edges = T.val) ↔
    ∃ b : GoodIncidentArrows G {r}, singletonRootedForestEquiv G r (incidentArrowForest G {r} b) ∈
      ({T} : Set G.SpanningTree) ∧
      σ ∈ terminalOutputEvent {r} (incidentCopyHead G) k (fun v i σ => σ (v, i)) b
  constructor
  · rintro ⟨s, hs, hsT⟩
    rw [hs'] at hs
    cases hs
    refine ⟨a, ?_, t, hrun, fun v => rfl⟩
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    change incidentArrowCopies G {r} a = T.val
    rw [← hedges, hsT]
  · rintro ⟨b, hb, l, hl, hlb⟩
    have hbl : (fun v => σ (v, l v)) = b.val := funext hlb
    have hlterm : terminal {r} (incidentCopyHead G) (fun v i => σ (v, i)) l := by
      intro c hc
      apply b.property c
      rw [← hbl]
      exact hc
    have htl := terminal_cursor_eq {r} (incidentCopyHead G) (fun v i => σ (v, i)) hrun hl ht hlterm
    have hab : a = b := by
      apply Subtype.ext
      change (fun v => σ (v, t v)) = b.val
      rw [htl]
      exact hbl
    refine ⟨s', hs', ?_⟩
    rw [hedges, hab]
    have h := congrArg Subtype.val (Set.mem_singleton_iff.mp hb)
    exact h

end
end FiniteAvalanches.Wilson.CopiedNetwork
