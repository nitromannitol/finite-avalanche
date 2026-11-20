import FiniteAvalanches.Wilson.Lattice.WiredDualFaceHistoryLimit
import FiniteAvalanches.Wilson.Lattice.HistoryEdgeRelabel
import FiniteAvalanches.Wilson.Lattice.OriginBranchAvoidsSink

/-! Confined face-square branch-history edges agree with centered-box edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Confined centered and face row histories have corresponding endpoints and erased vertices. -/
theorem rowBranchHistory_wiredDualFace_compatible_of_confined (B N : ℕ)
    (x : ℕ → FiniteWired.Active (B + 1)) (S : Set (FiniteWired.Active (B + 1)))
    (k : Cursor (FiniteWired.Active (B + 1))) (l : Cursor (WiredDualFace (B + 1)))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (hconf : ∀ i < n, ∀ j <
      (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (i + 1)).2.1,
      FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (x i)
        (branchHistoryCursor (freeDirectionHead (B + 1)) x k i
          (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows i)) (rows i) j).1)) :
    BranchHistory.ColorCompatible (freeDirectionHead (B + 1)) (wiredDualFaceDirectionHead (B + 1))
      x (fun i => wiredDualFaceInnerVertex (B + 1) (x i))
      (wiredDualFaceInnerVertex (B + 1)) Set.univ n
      (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows n) := by
  letI : Quiver (FiniteWired.Active (B + 1)) := instructionQuiver (freeDirectionHead (B + 1))
  letI : Quiver (WiredDualFace (B + 1)) := instructionQuiver (wiredDualFaceDirectionHead (B + 1))
  induction n with
  | zero => trivial
  | succ n ih =>
    have hpast : ∀ i < n, ∀ j <
        (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (i + 1)).2.1,
        FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (x i)
          (branchHistoryCursor (freeDirectionHead (B + 1)) x k i
            (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows i)) (rows i) j).1) :=
      fun i hi => hconf i (Nat.lt_succ_of_lt hi)
    let a := rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows n
    let T := branchHistoryRoots (freeDirectionHead (B + 1)) x S n a
    let c := branchHistoryCursor (freeDirectionHead (B + 1)) x k n a
    let t := boundedWordHit (freeDirectionHead (B + 1)) T (x n) c N (rows n)
    let p := stoppedDirectionHistory (fun _ => t) (rows n)
    have hc : ∀ j < t, FiniteWired.inBox B
        (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (x n) c (rows n) j).1) :=
      hconf n (Nat.lt_succ_self n)
    have he : wiredDualFaceInnerVertex (B + 1)
          (historyTrace (freeDirectionHead (B + 1)) (x n) p).1 =
        (historyTrace (wiredDualFaceDirectionHead (B + 1)) (wiredDualFaceInnerVertex (B + 1) (x n)) p).1 := by
      rw [historyTrace_stopped_fst (freeDirectionHead (B + 1)) (x n) (rows n) c t,
        historyTrace_stopped_fst (wiredDualFaceDirectionHead (B + 1))
          (wiredDualFaceInnerVertex (B + 1) (x n)) (rows n) l t]
      exact wiredDualFace_wordState_of_confined B (x n) c l (rows n) t hc t le_rfl
    have hw : (loopErase (historyTrace (freeDirectionHead (B + 1)) (x n) p).2).vertices.map
          (wiredDualFaceInnerVertex (B + 1)) =
        (loopErase (historyTrace (wiredDualFaceDirectionHead (B + 1))
          (wiredDualFaceInnerVertex (B + 1) (x n)) p).2).vertices := by
      have hp : ∀ i < t, p.extend i = (rows n) i := by
        intro i hi
        simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi]
      have hf := wordTrace_eq_of_prefix (freeDirectionHead (B + 1)) (x n) (rows n) p.extend t hp
      have hd := wordTrace_eq_of_prefix (wiredDualFaceDirectionHead (B + 1))
        (wiredDualFaceInnerVertex (B + 1) (x n)) (rows n) p.extend t hp
      change (loopErase (wordTrace (freeDirectionHead (B + 1)) (x n) p.extend t).2).vertices.map _ =
        (loopErase (wordTrace (wiredDualFaceDirectionHead (B + 1))
          (wiredDualFaceInnerVertex (B + 1) (x n)) p.extend t).2).vertices
      rw [hf, hd]
      exact wiredDualFace_wordTrace_loopErase_of_confined B (x n) c l (rows n) t hc
    change BranchHistory.ColorCompatible (freeDirectionHead (B + 1)) (wiredDualFaceDirectionHead (B + 1))
        x (fun i => wiredDualFaceInnerVertex (B + 1) (x i))
        (wiredDualFaceInnerVertex (B + 1)) Set.univ n a ∧
      (historyTrace (freeDirectionHead (B + 1)) (x n) p).1 ∈ Set.univ ∧
      wiredDualFaceInnerVertex (B + 1) (historyTrace (freeDirectionHead (B + 1)) (x n) p).1 =
        (historyTrace (wiredDualFaceDirectionHead (B + 1)) (wiredDualFaceInnerVertex (B + 1) (x n)) p).1 ∧
      (loopErase (historyTrace (freeDirectionHead (B + 1)) (x n) p).2).vertices.map
        (wiredDualFaceInnerVertex (B + 1)) =
          (loopErase (historyTrace (wiredDualFaceDirectionHead (B + 1))
            (wiredDualFaceInnerVertex (B + 1) (x n)) p).2).vertices
    exact ⟨ih hpast, Set.mem_univ _, he, hw⟩

/-- Confined face history edge sets are the images of centered-box history edges. -/
theorem rowBranchHistory_wiredDualFace_edges_map_of_confined (B N : ℕ)
    (x : ℕ → FiniteWired.Active (B + 1)) (S : Set (FiniteWired.Active (B + 1)))
    (k : Cursor (FiniteWired.Active (B + 1))) (l : Cursor (WiredDualFace (B + 1)))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (hconf : ∀ i < n, ∀ j <
      (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (i + 1)).2.1,
      FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (x i)
        (branchHistoryCursor (freeDirectionHead (B + 1)) x k i
          (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows i)) (rows i) j).1)) :
    (branchHistoryEdgeSet (freeDirectionHead (B + 1)) x n
      (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows n)).image
        (Sym2.map (wiredDualFaceInnerVertex (B + 1))) =
      branchHistoryEdgeSet (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (x i)) n
        (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows n) := by
  apply branchHistoryEdgeSet_map_eq (freeDirectionHead (B + 1)) (wiredDualFaceDirectionHead (B + 1))
    x (fun i => wiredDualFaceInnerVertex (B + 1) (x i))
    (wiredDualFaceInnerVertex (B + 1)) Set.univ n
  exact rowBranchHistory_wiredDualFace_compatible_of_confined B N x S k l rows n hconf

end
end FiniteAvalanches.Wilson.Lattice
