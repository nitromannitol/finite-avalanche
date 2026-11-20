import FiniteAvalanches.Wilson.CyclePopping.IncidentForestLaw
import FiniteAvalanches.Wilson.CyclePopping.StackExploration

/-! Finite prefix determination of terminal incident-copy forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open FiniteAvalanches.Trees
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

/-- A successful prefix and a terminal continuation have the same cursor on
all vertices attached by the prefix. -/
theorem stackExplore_terminal_cursor_on_attached {A : V → Type*}
    (head : (v : V) → A v → V) (σ : Stacks A) (R : Set V) (k t : Cursor V)
    (L : List V) (T : Set V) (j : Cursor V)
    (hrun : Relation.ReflTransGen (pop_step R head σ) k t) (ht : terminal R head σ t)
    (hexplore : stackExplore head σ R k L = some (T, j)) :
    ∀ v ∈ T, t v = j v := by
  obtain ⟨T', j', he, _, _, _, hcont, _⟩ := stackExplore_of_terminal R head σ k t hrun ht L
  rw [hexplore, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  intro v hv
  exact pop_run_root_cursor T head σ hcont hv

/-- Once both endpoints are attached, membership of an original edge copy in
the terminal forest is determined by the visible prefix arrows. -/
theorem terminal_incidentCopy_mem_iff_prefix (G : Multigraph V E) (R : Set V)
    (σ : Stacks (IncidentCopy G)) (k t : Cursor V) (L : List V) (T : Set V) (j : Cursor V)
    (hrun : Relation.ReflTransGen (pop_step R (incidentCopyHead G) σ) k t)
    (ht : terminal R (incidentCopyHead G) σ t)
    (hexplore : stackExplore (incidentCopyHead G) σ R k L = some (T, j))
    (e : E) (hleft : G.left e ∈ T) (hright : G.right e ∈ T) :
    e ∈ incidentArrowCopies G R ⟨fun v => σ v (t v), ht⟩ ↔
      ∃ v ∈ T, v ∉ R ∧ (σ v (j v)).val = e := by
  have hc := stackExplore_terminal_cursor_on_attached (incidentCopyHead G) σ R k t L T j hrun ht hexplore
  change e ∈ rootwardCopies R (fun v => (σ v (t v)).val) ↔ _
  simp only [rootwardCopies, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hvR, he⟩
    have hv : v ∈ T := by
      have hi := (σ v (t v)).property
      rw [he] at hi
      rcases hi with hi | hi
      · exact hi ▸ hleft
      · exact hi ▸ hright
    refine ⟨v, hv, hvR, ?_⟩
    rw [← hc v hv]
    exact he
  · rintro ⟨v, hv, hvR, he⟩
    refine ⟨v, hvR, ?_⟩
    rw [hc v hv]
    exact he

end
end FiniteAvalanches.Wilson.CyclePopping
