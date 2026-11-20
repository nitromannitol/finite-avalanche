import FiniteAvalanches.Wilson.Lattice.FreeBranchCoupling
import FiniteAvalanches.Wilson.Lattice.HistoryEdgeRelabel
import FiniteAvalanches.Wilson.Lattice.OriginBranchAvoidsSink

/-! Confined free-box branch-history edges agree with lattice edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The endpoint of a confined free-box history is the projected lattice endpoint. -/
theorem free_historyTrace_endpoint_of_confined (B : ℕ) (x : Site 2)
    (w : WalkDriver) (k : Cursor (FiniteWired.Active B)) (t : ℕ)
    (hbox : ∀ i ≤ t, FiniteWired.inBox B (position x w i)) :
    (historyTrace (freeDirectionHead B) (freeSite B x) (stoppedDirectionHistory (fun _ => t) w)).1 =
      freeSite B (position x w t) := by
  rw [historyTrace_stopped_fst (freeDirectionHead B) (freeSite B x) w k t]
  exact freeWordState_eq_of_confined B x w k t hbox t le_rfl

/-- Confined free and lattice row histories have matching endpoints and erased vertices. -/
theorem rowBranchHistory_free_compatible_of_confined (B N : ℕ) (x : ℕ → Site 2)
    (R : Set (Site 2)) (ka : Cursor (Site 2)) (kb : Cursor (FiniteWired.Active B))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (hbox : ∀ i < n, ∀ j ≤ (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j)) :
    BranchHistory.ColorCompatible (freeDirectionHead B) latticeDirectionHead
      (fun i => freeSite B (x i)) x FiniteWired.site Set.univ n
      (rowBranchHistory latticeDirectionHead x R ka N rows n) := by
  letI : Quiver (FiniteWired.Active B) := instructionQuiver (freeDirectionHead B)
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  induction n with
  | zero => trivial
  | succ n ih =>
    have hpast : ∀ i < n, ∀ j ≤ (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1,
        FiniteWired.inBox B (position (x i) (rows i) j) :=
      fun i hi => hbox i (Nat.lt_succ_of_lt hi)
    let a := rowBranchHistory latticeDirectionHead x R ka N rows n
    let S := branchHistoryRoots latticeDirectionHead x R n a
    let c := branchHistoryCursor latticeDirectionHead x ka n a
    let t := boundedWordHit latticeDirectionHead S (x n) c N (rows n)
    let p := stoppedDirectionHistory (fun _ => t) (rows n)
    have hconf : ∀ j ≤ t, FiniteWired.inBox B (position (x n) (rows n) j) :=
      hbox n (Nat.lt_succ_self n)
    have he := free_historyTrace_endpoint_of_confined B (x n) (rows n) kb t hconf
    have ha := historyTrace_stopped_lattice_endpoint (x n) (rows n) t
    have hw := free_historyTrace_loopErase_of_confined B (x n) (rows n) kb t hconf
    have hl := historyTrace_stopped_loopErase_vertices (x n) (rows n) t
    change BranchHistory.ColorCompatible (freeDirectionHead B) latticeDirectionHead
        (fun i => freeSite B (x i)) x FiniteWired.site Set.univ n a ∧
      (historyTrace (freeDirectionHead B) (freeSite B (x n)) p).1 ∈ Set.univ ∧
      FiniteWired.site (historyTrace (freeDirectionHead B) (freeSite B (x n)) p).1 =
        (historyTrace latticeDirectionHead (x n) p).1 ∧
      (loopErase (historyTrace (freeDirectionHead B) (freeSite B (x n)) p).2).vertices.map
        FiniteWired.site = (loopErase (historyTrace latticeDirectionHead (x n) p).2).vertices
    refine ⟨ih hpast, Set.mem_univ _, ?_, hw.trans hl.symm⟩
    rw [he, ha, site_freeSite_of_inBox B _ (hconf t le_rfl)]

/-- Confined free-box history edge sets map exactly to their lattice counterparts. -/
theorem rowBranchHistory_free_edges_map_of_confined (B N : ℕ) (x : ℕ → Site 2)
    (R : Set (Site 2)) (ka : Cursor (Site 2)) (kb : Cursor (FiniteWired.Active B))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (hbox : ∀ i < n, ∀ j ≤ (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j)) :
    (branchHistoryEdgeSet (freeDirectionHead B) (fun i => freeSite B (x i)) n
      (rowBranchHistory latticeDirectionHead x R ka N rows n)).image (Sym2.map FiniteWired.site) =
      branchHistoryEdgeSet latticeDirectionHead x n (rowBranchHistory latticeDirectionHead x R ka N rows n) := by
  apply branchHistoryEdgeSet_map_eq (freeDirectionHead B) latticeDirectionHead
    (fun i => freeSite B (x i)) x FiniteWired.site Set.univ n
  exact rowBranchHistory_free_compatible_of_confined B N x R ka kb rows n hbox

end
end FiniteAvalanches.Wilson.Lattice
