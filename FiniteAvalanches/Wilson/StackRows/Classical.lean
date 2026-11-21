import FiniteAvalanches.Wilson.StackRows.Tree

/-! Wilson's theorem for the classical protocol on a finite connected multigraph whose
parallel copies are distinct edges: walks from the first unretained vertex of an ordering
of the nonroot vertices, each using a fresh row of independent uniform incident copies,
loop-erased chronologically and attached, give a uniform spanning tree of copies. The
recorded history uses an embedding of the copies; success and the edges do not depend on
it, so the law is computed with the copies themselves as labels, where the classical and
stack protocols have the same law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CopiedNetwork

open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V E I : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Success, roots and edges of the classical protocol do not depend on the labels used
for the copies in the recorded history. -/
theorem classicalExplore_map_roots_edges {J : Type} (ι : E ↪ I) (κ : E ↪ J) (L : List V) :
    ∀ (s : State (V := V) (E := E) (I := I)) (s' : State (V := V) (E := E) (I := J)),
      s.roots = s'.roots → s.edges = s'.edges → ∀ ω : ℕ → Driver G,
      (classicalExplore G ι s L ω).map (fun t => (t.roots, t.edges)) =
        (classicalExplore G κ s' L ω).map (fun t => (t.roots, t.edges)) := by
  induction L with
  | nil =>
    intro s s' hr he ω
    simp only [classicalExplore, Option.map_some, hr, he]
  | cons x xs ih =>
    intro s s' hr he ω
    obtain ⟨R', hR', E', H'⟩ := s'
    simp only at hr he
    subst hr he
    by_cases hx : x ∈ s.roots
    · have h1 : classicalExplore G ι s (x :: xs) ω = classicalExplore G ι s xs ω := by
        simp only [classicalExplore, if_pos hx]
      have h2 : classicalExplore G κ ⟨s.roots, hR', s.edges, H'⟩ (x :: xs) ω =
          classicalExplore G κ ⟨s.roots, hR', s.edges, H'⟩ xs ω := by
        simp only [classicalExplore]
        exact if_pos hx
      rw [h1, h2]
      exact ih s _ rfl rfl ω
    · have h1 : classicalExplore G ι s (x :: xs) ω = (query G ι s x (ω 0)).bind
          (fun t => classicalExplore G ι t xs (fun i => ω (i + 1))) := by
        simp only [classicalExplore, if_neg hx]
      have h2 : classicalExplore G κ ⟨s.roots, hR', s.edges, H'⟩ (x :: xs) ω =
          (query G κ ⟨s.roots, hR', s.edges, H'⟩ x (ω 0)).bind
            (fun t => classicalExplore G κ t xs (fun i => ω (i + 1))) := by
        simp only [classicalExplore]
        exact if_neg hx
      rw [h1, h2]
      by_cases hh : hits G s.roots x (ω 0)
      · have q1 : query G ι s x (ω 0) = some (attachAt G ι s x (ω 0) (Nat.find hh)) := by
          rw [query, if_neg hx, dif_pos hh]
        have q2 : query G κ ⟨s.roots, hR', s.edges, H'⟩ x (ω 0) =
            some (attachAt G κ ⟨s.roots, hR', s.edges, H'⟩ x (ω 0) (Nat.find hh)) := by
          unfold query
          exact (if_neg hx).trans (dif_pos hh)
        rw [q1, q2, Option.bind_some, Option.bind_some]
        exact ih _ _ rfl rfl _
      · have q1 : query G ι s x (ω 0) = none := by
          rw [query, if_neg hx, dif_neg hh]
        have q2 : query G κ ⟨s.roots, hR', s.edges, H'⟩ x (ω 0) = none := by
          unfold query
          exact (if_neg hx).trans (dif_neg hh)
        rw [q1, q2]
        rfl

/-- The tree events of the classical protocol do not depend on the history labels. -/
theorem classicalExplore_tree_event_eq {J : Type} (ι : E ↪ I) (κ : E ↪ J) (r : V)
    (order : List V) (T : G.SpanningTree) :
    {ω : ℕ → Driver G | ∃ s, classicalExplore G ι
        (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω = some s ∧ s.edges = T.val} =
      {ω | ∃ s, classicalExplore G κ
        (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω = some s ∧ s.edges = T.val} := by
  ext ω
  have h := classicalExplore_map_roots_edges G ι κ order
    (initialState ⟨{r}, Set.singleton_nonempty r⟩) (initialState ⟨{r}, Set.singleton_nonempty r⟩)
    rfl rfl ω
  constructor
  · rintro ⟨s, hs, hT⟩
    rw [hs, Option.map_some] at h
    obtain ⟨s', hs', hp⟩ := Option.map_eq_some_iff.mp h.symm
    exact ⟨s', hs', (congrArg Prod.snd hp).trans hT⟩
  · rintro ⟨s, hs, hT⟩
    rw [hs, Option.map_some] at h
    obtain ⟨s', hs', hp⟩ := Option.map_eq_some_iff.mp h
    exact ⟨s', hs', (congrArg Prod.snd hp).trans hT⟩

/-- **Wilson's theorem** for the classical protocol: the edges of the output are a uniform
spanning tree of copies. Lyons–Peres, *Probability on Trees and Networks*, Theorem 4.1. -/
theorem classicalExplore_tree_probability [Nontrivial V]
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) (ι : E ↪ I) (r : V) (order : List V)
    (hspan : ∀ v : V, v ≠ r → v ∈ order) (T : G.SpanningTree) :
    driversLaw G (uniformLetterLaw G hconn)
        {ω | ∃ s, classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω =
            some s ∧ s.edges = T.val} =
      (Fintype.card G.SpanningTree : ℝ≥0∞)⁻¹ := by
  letI : ∀ v, Nonempty (IncidentCopy G v) := fun v => incident_nonempty G hconn v
  rw [classicalExplore_tree_event_eq G ι (Function.Embedding.refl E) r order T]
  have hB := (stackRun_law G (Function.Embedding.refl E) hconn order
    (initialState ⟨{r}, Set.singleton_nonempty r⟩) 0
    {o | ∃ s, o = some s ∧ s.edges = T.val}).2
  simp only [Set.mem_setOf_eq] at hB
  rw [← hB]
  exact variableStackLaw_stackRun_tree G (Function.Embedding.refl E) hconn r order hspan 0 T

end
end FiniteAvalanches.Wilson.CopiedNetwork
