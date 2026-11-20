import FiniteAvalanches.Wilson.Lattice.FreeTerminalHistory
import FiniteAvalanches.Wilson.Lattice.IncidentHistoryEdges
import FiniteAvalanches.Wilson.Lattice.BoundedHistoryFirstHit

/-! Free terminal copies are determined by their finite branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeHistoryEdges (N : ℕ) :
    DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- Each unordered endpoint pair specifies a unique original free-box copy. -/
theorem freeBoxGraph_endpointPair_injective (B : ℕ) :
    Function.Injective (fun e : FiniteWired.InteriorEdge B =>
      s((freeBoxGraph B).left e, (freeBoxGraph B).right e)) := by
  intro e f h
  apply interiorEdge_injective B
  apply Subtype.ext
  have hm := congrArg (Sym2.map (FiniteWired.site : FiniteWired.Active B → Site 2)) h
  change s(FiniteWired.site e.val.1, FiniteWired.site e.val.2) =
    s(FiniteWired.site f.val.1, FiniteWired.site f.val.2)
  simpa only [freeBoxGraph, Multigraph.ofEndpoints, Sym2.map_mk] using hm

/-- On attached endpoints, free terminal copied-edge membership is exactly
membership of its endpoint pair in the retained branch-history edges. -/
theorem freeTerminalCopy_mem_iff_branchHistoryEdgeSet (B : ℕ)
    (x : ℕ → FiniteWired.Active (B + 1)) (k t : Cursor (FiniteWired.Active (B + 1))) (N n : ℕ)
    (σ : (p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1)
    (hrun : Relation.ReflTransGen (pop_step (freeOriginAndBoundary B)
      (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k t)
    (ht : terminal (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1)))
      (fun v i => σ (v, i)) t)
    (hhit : ∀ i < n, (boundedBranchHistory (freeDirectionHead (B + 1)) x
      (freeOriginAndBoundary B) k N (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ))
        (i + 1)).2.1 < N)
    (e : FiniteWired.InteriorEdge (B + 1))
    (hleft : (freeBoxGraph (B + 1)).left e ∈ branchHistoryRoots (freeDirectionHead (B + 1)) x
      (freeOriginAndBoundary B) n (boundedBranchHistory (freeDirectionHead (B + 1)) x
        (freeOriginAndBoundary B) k N (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)) n))
    (hright : (freeBoxGraph (B + 1)).right e ∈ branchHistoryRoots (freeDirectionHead (B + 1)) x
      (freeOriginAndBoundary B) n (boundedBranchHistory (freeDirectionHead (B + 1)) x
        (freeOriginAndBoundary B) k N (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)) n)) :
    e ∈ incidentArrowCopies (freeBoxGraph (B + 1)) (freeOriginAndBoundary B)
        ⟨fun v => σ (v, t v), ht⟩ ↔
      s((freeBoxGraph (B + 1)).left e, (freeBoxGraph (B + 1)).right e) ∈
        branchHistoryEdgeSet (freeDirectionHead (B + 1)) x n
          (boundedBranchHistory (freeDirectionHead (B + 1)) x (freeOriginAndBoundary B) k N
            (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)) n) := by
  let τ := padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)
  have hfirst := boundedBranchHistory_firstHits_of_hits (freeDirectionHead (B + 1)) x
    (freeOriginAndBoundary B) k N n τ hhit
  have hreal := freeIncident_terminal_realizes_branchHistory B x k t N n σ hrun ht hhit
  change e ∈ rootwardCopies (freeOriginAndBoundary B) (fun v => (σ (v, t v)).val) ↔ _
  exact incidentCopy_mem_iff_branchHistoryEdgeSet (freeBoxGraph (B + 1)) (freeOriginAndBoundary B)
    (freeDirectionHead (B + 1)) x n _ (fun v => σ (v, t v)) (fun v => τ (v, t v)) e
    (freeBoxGraph_endpointPair_injective (B + 1))
    (fun v hv => (freeIncident_paddedDirections_successors B σ v hv (t v)).symm)
    hfirst hreal hleft hright

end
end FiniteAvalanches.Wilson.Lattice
