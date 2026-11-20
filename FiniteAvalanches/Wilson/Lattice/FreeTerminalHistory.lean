import FiniteAvalanches.Wilson.Lattice.FreeFiniteLaw
import FiniteAvalanches.Wilson.Lattice.TerminalHistoryRealization
import FiniteAvalanches.Wilson.CyclePopping.PopAlphabetCoupling

/-! Free incident-stack terminal forests realize direction-stack branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeTerminalHistory (N : ℕ) :
    DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- At every nonroot, free incident and padded direction stacks have the same successor. -/
theorem freeIncident_paddedDirections_successors (B : ℕ)
    (σ : (p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1)
    (v : FiniteWired.Active (B + 1)) (hv : v ∉ freeOriginAndBoundary B) (i : ℕ) :
    incidentCopyHead (freeBoxGraph (B + 1)) v (σ (v, i)) =
      freeDirectionHead (B + 1) v (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ) (v, i)) := by
  have hin : FiniteWired.inBox B (FiniteWired.site v) := by
    by_contra hn
    exact hv (Set.mem_union_right _ hn)
  simp only [padFreeInteriorStacks, dif_pos hin, freeInteriorDirectionStacks]
  have h := freeInteriorDirection_head_eq B v hin ((freeInteriorDirectionEquiv B v hin).symm (σ (v, i)))
  simpa only [Equiv.apply_symm_apply] using h

/-- Incident and padded direction stacks have the same legal runs and terminal cursors. -/
theorem freeIncident_paddedDirections_terminal (B : ℕ)
    (σ : (p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1)
    (k t : Cursor (FiniteWired.Active (B + 1))) :
    (Relation.ReflTransGen (pop_step (freeOriginAndBoundary B)
        (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k t ↔
      Relation.ReflTransGen (pop_step (freeOriginAndBoundary B) (freeDirectionHead (B + 1))
        (fun v i => padFreeInteriorStacks B (freeInteriorDirectionStacks B σ) (v, i))) k t) ∧
    (terminal (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1)))
        (fun v i => σ (v, i)) t ↔
      terminal (freeOriginAndBoundary B) (freeDirectionHead (B + 1))
        (fun v i => padFreeInteriorStacks B (freeInteriorDirectionStacks B σ) (v, i)) t) := by
  refine ⟨pop_run_iff_of_matching_successors _ _ _ _ _ _ _ ?_,
    terminal_iff_of_matching_successors _ _ _ _ _ _ ?_⟩ <;>
    exact freeIncident_paddedDirections_successors B σ

/-- A terminal free incident stack realizes its successful finite direction history. -/
theorem freeIncident_terminal_realizes_branchHistory (B : ℕ)
    (x : ℕ → FiniteWired.Active (B + 1)) (k t : Cursor (FiniteWired.Active (B + 1))) (N n : ℕ)
    (σ : (p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1)
    (hrun : Relation.ReflTransGen (pop_step (freeOriginAndBoundary B)
      (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k t)
    (ht : terminal (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1)))
      (fun v i => σ (v, i)) t)
    (h : ∀ i < n, (boundedBranchHistory (freeDirectionHead (B + 1)) x (freeOriginAndBoundary B)
      k N (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)) (i + 1)).2.1 < N) :
    BranchHistory.Realizes (freeDirectionHead (B + 1)) x
      (fun v => padFreeInteriorStacks B (freeInteriorDirectionStacks B σ) (v, t v)) n
      (boundedBranchHistory (freeDirectionHead (B + 1)) x (freeOriginAndBoundary B)
        k N (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)) n) := by
  have hmatch := freeIncident_paddedDirections_terminal B σ k t
  exact terminal_realizes_branchHistory (freeDirectionHead (B + 1)) (freeOriginAndBoundary B) x k t N n
    (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)) (hmatch.1.mp hrun) (hmatch.2.mp ht) h

end
end FiniteAvalanches.Wilson.Lattice
