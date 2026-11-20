import FiniteAvalanches.Wilson.CyclePopping.TerminalPrefixCopies

/-! Coupling terminal copied forests under nested root sets. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open FiniteAvalanches.Trees
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

/-- If nested-root explorations share a prefix cursor, their terminal copied
forests agree on edges attached by the smaller exploration whose endpoints
are not among the extra roots. -/
theorem terminal_incidentCopy_mem_iff_of_nested_prefix (G : Multigraph V E)
    (R S : Set V) (hRS : R ⊆ S) (σ : Stacks (IncidentCopy G)) (k t u : Cursor V)
    (L : List V) (T : Set V) (j : Cursor V)
    (hrun : Relation.ReflTransGen (pop_step R (incidentCopyHead G) σ) k t)
    (ht : terminal R (incidentCopyHead G) σ t)
    (hsrun : Relation.ReflTransGen (pop_step S (incidentCopyHead G) σ) k u)
    (hu : terminal S (incidentCopyHead G) σ u)
    (hexplore : stackExplore (incidentCopyHead G) σ R k L = some (T, j))
    (hsexplore : stackExplore (incidentCopyHead G) σ S k L = some (S ∪ T, j))
    (e : E) (hleft : G.left e ∈ T) (hright : G.right e ∈ T)
    (hle : G.left e ∈ S → G.left e ∈ R)
    (hre : G.right e ∈ S → G.right e ∈ R) :
    e ∈ incidentArrowCopies G R ⟨fun v => σ v (t v), ht⟩ ↔
      e ∈ incidentArrowCopies G S ⟨fun v => σ v (u v), hu⟩ := by
  rw [terminal_incidentCopy_mem_iff_prefix G R σ k t L T j hrun ht hexplore e hleft hright,
    terminal_incidentCopy_mem_iff_prefix G S σ k u L (S ∪ T) j hsrun hu hsexplore e
      (Or.inr hleft) (Or.inr hright)]
  constructor
  · rintro ⟨v, hvT, hvR, he⟩
    refine ⟨v, Or.inr hvT, ?_, he⟩
    intro hvS
    have hi := (σ v (j v)).property
    rw [he] at hi
    rcases hi with hi | hi
    · exact hvR (hi ▸ hle (hi.symm ▸ hvS))
    · exact hvR (hi ▸ hre (hi.symm ▸ hvS))
  · rintro ⟨v, hv, hvS, he⟩
    refine ⟨v, ?_, fun hvR => hvS (hRS hvR), he⟩
    rcases hv with hvS' | hvT
    · exact (hvS hvS').elim
    · exact hvT

end
end FiniteAvalanches.Wilson.CyclePopping
