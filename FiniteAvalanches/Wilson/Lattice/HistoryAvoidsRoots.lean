import FiniteAvalanches.Wilson.Lattice.HistoryFirstHitTrace
import FiniteAvalanches.Wilson.Lattice.OriginSafeHistoryLaw
import FiniteAvalanches.Wilson.CyclePopping.AvoidExtraAppend

/-! Safe finite branch histories certify root-avoiding stack explorations. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- If each bounded branch hits before its horizon and its endpoint avoids the
extra roots, the actual finite stack exploration avoids those roots. -/
theorem stackExploreAvoidsRoots_of_boundedBranchHistory
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R D : Set V)
    (k : Cursor V) (N n : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (hhit : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N)
    (havoid : BranchHistory.EndsAvoid head x D n (boundedBranchHistory head x R k N σ n)) :
    stackExploreAvoidsRoots head (fun v i => σ (v, i)) D R k ((List.range n).map x) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hpast : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N :=
      fun i hi => hhit i (Nat.lt_succ_of_lt hi)
    let a := boundedBranchHistory head x R k N σ n
    let S := branchHistoryRoots head x R n a
    let c := branchHistoryCursor head x k n a
    let j := branchHistoryErasedCursor head x k n a
    let t := boundedWordHit head S (x n) c N (readingLetter head (x n) c σ)
    let p := stoppedDirectionHistory (boundedWordHit head S (x n) c N) (readingLetter head (x n) c σ)
    have hlast : t < N := hhit n (Nat.lt_succ_self n)
    have hexplore := stackExplore_eq_historyErasedCursor head x R k N n σ hpast
    have hc : ∀ v, v ∉ S → j v = c v := hexplore.2
    change BranchHistory.EndsAvoid head x D n a ∧ (historyTrace head (x n) p).1 ∉ D at havoid
    have hprefix := ih hpast havoid.1
    obtain ⟨hh, htrace⟩ := firstHitTrace_eq_history_of_boundedHit head S (x n) j c N σ hc hlast
    have hend : (instructionTrace head (fun v i => σ (v, i)) j (x n) (Nat.find hh)).1 ∉ D := by
      rw [htrace]
      exact havoid.2
    have hone : stackExploreAvoidsRoots head (fun v i => σ (v, i)) D S j [x n] := by
      exact ⟨hh, hend, trivial⟩
    rw [List.range_succ, List.map_append]
    exact stackExploreAvoidsRoots_append head (fun v i => σ (v, i)) D R k
      ((List.range n).map x) [x n] S j hprefix hexplore.1 hone

end
end FiniteAvalanches.Wilson.Lattice
