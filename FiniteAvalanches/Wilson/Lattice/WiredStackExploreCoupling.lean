import FiniteAvalanches.Wilson.Lattice.WiredActiveStackCoupling
import FiniteAvalanches.Wilson.CyclePopping.StackAlphabetCoupling
import FiniteAvalanches.Wilson.CyclePopping.RootSetCoupling

/-! Coupling incident-copy and direction explorations before the wired sink. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Stopped explorations agree when the wired sink is among their initial
roots, even though its incident alphabet can have a different size. -/
theorem incidentStackExplore_eq_paddedDirections (B : ℕ)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1)
    (R : Set (FiniteWired.Vertex B)) (hR : none ∈ R)
    (k : Cursor (FiniteWired.Vertex B)) (L : List (FiniteWired.Vertex B)) :
    stackExplore (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i)) R k L =
      stackExplore (wiredHead B)
        (fun v i => padActiveDirectionStacks B (wiredActiveDirectionStacks B σ) (v, i)) R k L := by
  apply stackExplore_eq_of_matching_successors
  intro v hv i
  cases v with
  | none => exact (hv hR).elim
  | some x =>
    exact incidentCopyHead_eq_wiredHead x (σ (some x, i))

/-- A direction-stack exploration stopped at the wired sink is insensitive
to all entries of the sink stack. -/
theorem directionStackExplore_eq_padActive (B : ℕ)
    (σ : FiniteWired.Vertex B × ℕ → FiniteWired.Direction)
    (R : Set (FiniteWired.Vertex B)) (hR : none ∈ R)
    (k : Cursor (FiniteWired.Vertex B)) (L : List (FiniteWired.Vertex B)) :
    stackExplore (wiredHead B) (fun v i => σ (v, i)) R k L =
      stackExplore (wiredHead B)
        (fun v i => padActiveDirectionStacks B (activeDirectionProjection B σ) (v, i)) R k L := by
  apply stackExplore_eq_of_matching_successors
  intro v hv i
  cases v with
  | none => exact (hv hR).elim
  | some x => rfl

/-- Any measurable event of a wired exploration stopped at the sink has the
same probability for incident-copy stacks and lattice direction stacks. -/
theorem variableStackLaw_stackExplore_event_eq (B : ℕ)
    (R : Set (FiniteWired.Vertex B)) (hR : none ∈ R)
    (k : Cursor (FiniteWired.Vertex B)) (L : List (FiniteWired.Vertex B))
    (P : Option (Set (FiniteWired.Vertex B) × Cursor (FiniteWired.Vertex B)) → Prop)
    (hP : MeasurableSet {σ : FiniteWired.Vertex B × ℕ → FiniteWired.Direction |
      P (stackExplore (wiredHead B) (fun v i => σ (v, i)) R k L)}) :
    variableStackLaw (IncidentCopy (WiredTrees.graph B))
      {σ | P (stackExplore (incidentCopyHead (WiredTrees.graph B))
        (fun v i => σ (v, i)) R k L)} =
    directionStackLaw (FiniteWired.Vertex B)
      {σ | P (stackExplore (wiredHead B) (fun v i => σ (v, i)) R k L)} := by
  let E : Set (FiniteWired.Vertex B × ℕ → FiniteWired.Direction) :=
    {σ | P (stackExplore (wiredHead B) (fun v i => σ (v, i)) R k L)}
  have hstable : ∀ σ, padActiveDirectionStacks B (activeDirectionProjection B σ) ∈ E ↔ σ ∈ E := by
    intro σ
    change P (stackExplore (wiredHead B)
      (fun v i => padActiveDirectionStacks B (activeDirectionProjection B σ) (v, i)) R k L) ↔
      P (stackExplore (wiredHead B) (fun v i => σ (v, i)) R k L)
    rw [← directionStackExplore_eq_padActive B σ R hR k L]
  have he := variableStackLaw_active_event_eq B E hP hstable
  have hset : {σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1 |
      P (stackExplore (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i)) R k L)} =
      {σ | padActiveDirectionStacks B (wiredActiveDirectionStacks B σ) ∈ E} := by
    ext σ
    change P (stackExplore (incidentCopyHead (WiredTrees.graph B))
      (fun v i => σ (v, i)) R k L) ↔
      P (stackExplore (wiredHead B)
        (fun v i => padActiveDirectionStacks B (wiredActiveDirectionStacks B σ) (v, i)) R k L)
    rw [incidentStackExplore_eq_paddedDirections B σ R hR k L]
  rw [hset]
  exact he

end
end FiniteAvalanches.Wilson.Lattice
