import FiniteAvalanches.Wilson.Lattice.WiredDualFaceSafeTerminal
import FiniteAvalanches.Wilson.Lattice.TerminalHistoryRealization
import FiniteAvalanches.Wilson.CyclePopping.PopAlphabetCoupling

/-! Face incident-stack terminal forests realize direction-stack histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- At nonroots the face incident and padded direction stacks have the same successor. -/
theorem wiredDualFaceIncident_paddedDirections_successors (B : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (v : WiredDualFace (B + 1)) (hv : v ∉ wiredDualFaceOriginAndBoundary B) (i : ℕ) :
    incidentCopyHead (wiredDualFaceGraph (B + 1)) v (σ (v, i)) =
      wiredDualFaceDirectionHead (B + 1) v
        (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) (v, i)) := by
  have hin : FiniteWired.inBox B (wiredDualFaceSite v) := by
    by_contra hn
    exact hv (Set.mem_union_right _ hn)
  exact wiredDualFace_paddedIncident_successor B σ v hin i

/-- Incident and padded direction stacks have the same legal runs and terminal cursors. -/
theorem wiredDualFaceIncident_paddedDirections_terminal (B : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (k t : Cursor (WiredDualFace (B + 1))) :
    (Relation.ReflTransGen (pop_step (wiredDualFaceOriginAndBoundary B)
        (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k t ↔
      Relation.ReflTransGen (pop_step (wiredDualFaceOriginAndBoundary B) (wiredDualFaceDirectionHead (B + 1))
        (fun v i => padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) (v, i))) k t) ∧
    (terminal (wiredDualFaceOriginAndBoundary B) (incidentCopyHead (wiredDualFaceGraph (B + 1)))
        (fun v i => σ (v, i)) t ↔
      terminal (wiredDualFaceOriginAndBoundary B) (wiredDualFaceDirectionHead (B + 1))
        (fun v i => padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) (v, i)) t) := by
  refine ⟨pop_run_iff_of_matching_successors _ _ _ _ _ _ _ ?_,
    terminal_iff_of_matching_successors _ _ _ _ _ _ ?_⟩ <;>
    exact wiredDualFaceIncident_paddedDirections_successors B σ

/-- A terminal face incident stack realizes every successful finite direction history. -/
theorem wiredDualFaceIncident_terminal_realizes_branchHistory (B : ℕ)
    (x : ℕ → WiredDualFace (B + 1)) (k t : Cursor (WiredDualFace (B + 1))) (N n : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (hrun : Relation.ReflTransGen (pop_step (wiredDualFaceOriginAndBoundary B)
      (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k t)
    (ht : terminal (wiredDualFaceOriginAndBoundary B) (incidentCopyHead (wiredDualFaceGraph (B + 1)))
      (fun v i => σ (v, i)) t)
    (h : ∀ i < n, (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) x
      (wiredDualFaceOriginAndBoundary B) k N
      (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)) (i + 1)).2.1 < N) :
    BranchHistory.Realizes (wiredDualFaceDirectionHead (B + 1)) x
      (fun v => padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) (v, t v)) n
      (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) x (wiredDualFaceOriginAndBoundary B)
        k N (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)) n) := by
  have hmatch := wiredDualFaceIncident_paddedDirections_terminal B σ k t
  exact terminal_realizes_branchHistory (wiredDualFaceDirectionHead (B + 1))
    (wiredDualFaceOriginAndBoundary B) x k t N n
    (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ))
    (hmatch.1.mp hrun) (hmatch.2.mp ht) h

end
end FiniteAvalanches.Wilson.Lattice
