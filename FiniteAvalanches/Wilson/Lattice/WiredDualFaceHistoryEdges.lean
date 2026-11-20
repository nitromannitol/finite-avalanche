import FiniteAvalanches.Wilson.Lattice.WiredDualFaceTerminalHistory
import FiniteAvalanches.Wilson.Lattice.IncidentHistoryEdges
import FiniteAvalanches.Wilson.Lattice.BoundedHistoryFirstHit

/-! Face-square terminal copies are determined by finite branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceHistoryEdges (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- On attached endpoints, face terminal copied-edge membership is exactly
membership of its endpoint pair in the retained branch-history edges. -/
theorem wiredDualFaceTerminalCopy_mem_iff_branchHistoryEdgeSet (B : ℕ)
    (x : ℕ → WiredDualFace (B + 1)) (k t : Cursor (WiredDualFace (B + 1))) (N n : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (hrun : Relation.ReflTransGen (pop_step (wiredDualFaceOriginAndBoundary B)
      (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k t)
    (ht : terminal (wiredDualFaceOriginAndBoundary B) (incidentCopyHead (wiredDualFaceGraph (B + 1)))
      (fun v i => σ (v, i)) t)
    (hhit : ∀ i < n, (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) x
      (wiredDualFaceOriginAndBoundary B) k N
      (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)) (i + 1)).2.1 < N)
    (e : FiniteWired.Edge (B + 1))
    (hleft : (wiredDualFaceGraph (B + 1)).left e ∈ branchHistoryRoots
      (wiredDualFaceDirectionHead (B + 1)) x (wiredDualFaceOriginAndBoundary B) n
      (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) x (wiredDualFaceOriginAndBoundary B) k N
        (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)) n))
    (hright : (wiredDualFaceGraph (B + 1)).right e ∈ branchHistoryRoots
      (wiredDualFaceDirectionHead (B + 1)) x (wiredDualFaceOriginAndBoundary B) n
      (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) x (wiredDualFaceOriginAndBoundary B) k N
        (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)) n)) :
    e ∈ incidentArrowCopies (wiredDualFaceGraph (B + 1)) (wiredDualFaceOriginAndBoundary B)
        ⟨fun v => σ (v, t v), ht⟩ ↔
      s((wiredDualFaceGraph (B + 1)).left e, (wiredDualFaceGraph (B + 1)).right e) ∈
        branchHistoryEdgeSet (wiredDualFaceDirectionHead (B + 1)) x n
          (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) x (wiredDualFaceOriginAndBoundary B) k N
            (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)) n) := by
  let τ := padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)
  have hfirst := boundedBranchHistory_firstHits_of_hits (wiredDualFaceDirectionHead (B + 1)) x
    (wiredDualFaceOriginAndBoundary B) k N n τ hhit
  have hreal := wiredDualFaceIncident_terminal_realizes_branchHistory B x k t N n σ hrun ht hhit
  change e ∈ rootwardCopies (wiredDualFaceOriginAndBoundary B) (fun v => (σ (v, t v)).val) ↔ _
  exact incidentCopy_mem_iff_branchHistoryEdgeSet (wiredDualFaceGraph (B + 1))
    (wiredDualFaceOriginAndBoundary B) (wiredDualFaceDirectionHead (B + 1)) x n _
    (fun v => σ (v, t v)) (fun v => τ (v, t v)) e
    (wiredDualFaceGraph_endpointPair_injective (B + 1))
    (fun v hv => (wiredDualFaceIncident_paddedDirections_successors B σ v hv (t v)).symm)
    hfirst hreal hleft hright

end
end FiniteAvalanches.Wilson.Lattice
