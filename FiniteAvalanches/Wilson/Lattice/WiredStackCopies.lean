import FiniteAvalanches.Wilson.Lattice.WiredStack
import FiniteAvalanches.Wilson.CopiedWalk
import FiniteAvalanches.Sandpile.Components.Incident

/-! Every wired direction stack instruction retains its original edge copy. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical

noncomputable section

/-- The endpoints of a direction copy are the starting vertex and its wired successor. -/
theorem wiredHead_direction_endpoints {N : ℕ} (x : FiniteWired.Active N)
    (d : FiniteWired.Direction) :
    ((FiniteWired.endpoints (FiniteWired.directionEdge x d)).1 = some x ∧
      (FiniteWired.endpoints (FiniteWired.directionEdge x d)).2 = wiredHead N (some x) d) ∨
    ((FiniteWired.endpoints (FiniteWired.directionEdge x d)).2 = some x ∧
      (FiniteWired.endpoints (FiniteWired.directionEdge x d)).1 = wiredHead N (some x) d) := by
  rcases d with ⟨i, b⟩
  cases b
  · simp only [wiredHead, FiniteWired.step, Bool.false_eq_true, if_false, ← sub_eq_add_neg]
    by_cases hb : FiniteWired.inBox N (FiniteWired.site x - unit i)
    · simp [FiniteWired.directionEdge, FiniteWired.endpoints, wiredSite, hb]
    · simp [FiniteWired.directionEdge, FiniteWired.endpoints, wiredSite, hb]
  · simp only [wiredHead, FiniteWired.step, if_true]
    by_cases hb : FiniteWired.inBox N (FiniteWired.site x + unit i)
    · simp [FiniteWired.directionEdge, FiniteWired.endpoints, wiredSite, hb]
    · simp [FiniteWired.directionEdge, FiniteWired.endpoints, wiredSite, hb]

/-- A lattice direction is the corresponding literal incident copy in the wired graph. -/
def wiredDirectionIncident {N : ℕ} (x : FiniteWired.Active N)
    (d : FiniteWired.Direction) : Incident (WiredTrees.graph N) (some x) :=
  ⟨FiniteWired.directionEdge x d, Components.direction_edge_incident x d⟩

/-- The successor of the incident copy is the wired lattice successor. -/
theorem wiredDirectionIncident_other {N : ℕ} (x : FiniteWired.Active N)
    (d : FiniteWired.Direction) :
    other (WiredTrees.graph N) (some x) (wiredDirectionIncident x d) = wiredHead N (some x) d := by
  rcases wiredHead_direction_endpoints x d with h | h
  · simp only [other, wiredDirectionIncident, WiredTrees.graph, Multigraph.ofEndpoints, h.1,
      if_true, h.2]
  · have hn : (FiniteWired.endpoints (FiniteWired.directionEdge x d)).1 ≠ some x := by
      intro he
      exact FiniteWired.endpoints_ne _ (he.trans h.1.symm)
    simp only [other, wiredDirectionIncident, WiredTrees.graph, Multigraph.ofEndpoints]
    rw [if_neg hn, h.2]

/-- The four directions biject with the four individual incident copies. -/
def wiredDirectionIncidentEquiv {N : ℕ} (x : FiniteWired.Active N) :
    FiniteWired.Direction ≃ Incident (WiredTrees.graph N) (some x) :=
  Equiv.ofBijective (wiredDirectionIncident x) ⟨by
    intro d e h
    exact Components.direction_edge_injective x (congrArg Subtype.val h), by
    intro e
    have hi : Components.incident x e.val := e.property
    obtain ⟨d, hd⟩ := Components.exists_direction_of_incident x e.val hi
    exact ⟨d, Subtype.ext hd⟩⟩

end
end FiniteAvalanches.Wilson.Lattice
