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

end
end FiniteAvalanches.Wilson.Lattice
