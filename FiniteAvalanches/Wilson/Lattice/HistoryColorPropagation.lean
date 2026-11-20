import FiniteAvalanches.Wilson.Lattice.HistoryFirstHit
import FiniteAvalanches.Wilson.Lattice.LatticeBranchHorizon
import FiniteAvalanches.Wilson.Lattice.HistoryRootward

/-! Propagating root colors along finite first-hit branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Propagate the endpoint color along each retained branch of a history. -/
def branchHistoryColor (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (seed : V → Option Bool) : (n : ℕ) → BranchHistory n → V → Option Bool
  | 0, _ => seed
  | n + 1, h => by
    letI : Quiver V := instructionQuiver head
    let old := branchHistoryColor head x seed n h.1
    let trace := historyTrace head (x n) h.2
    exact fun v => if v ∈ departures (loopErase trace.2) then old trace.1 else old v

/-- For a realized first-hit history, propagated colors are the colors of the
first roots reached by the selected arrows. -/
theorem branchHistoryColor_eq_firstRoot (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (seed : V → Option Bool) (color : V → Bool)
    (n : ℕ) (h : BranchHistory n) (a : V → FiniteWired.Direction)
    (hhit : ∀ v, ∃ i, (fun v => head v (a v))^[i] v ∈ R)
    (hseed : ∀ v ∈ R, seed v = some (color v))
    (hfirst : BranchHistory.FirstHits head x R n h)
    (ha : BranchHistory.Realizes head x a n h) :
    ∀ v ∈ branchHistoryRoots head x R n h,
      branchHistoryColor head x seed n h v =
        some (color (firstRoot R (fun v => head v (a v)) hhit v)) := by
  letI : Quiver V := instructionQuiver head
  induction n with
  | zero =>
    intro v hv
    change seed v = some (color (firstRoot R (fun v => head v (a v)) hhit v))
    rw [firstRoot_of_mem R _ hhit hv]
    exact hseed v hv
  | succ n ih =>
    change BranchHistory.FirstHits head x R n h.1 ∧ _ at hfirst
    change BranchHistory.Realizes head x a n h.1 ∧ _ at ha
    let S := branchHistoryRoots head x R n h.1
    let q := loopErase (historyTrace head (x n) h.2).2
    have hend : (historyTrace head (x n) h.2).1 ∈ S := hfirst.2.1
    have havoid : ∀ v ∈ departures q, v ∉ R := by
      intro v hv hvR
      exact hfirst.2.2 v hv (branchHistoryRoots_initial_subset head x R n h.1 hvR)
    have hfollow := selected_follows (instructionArrowStacks head (fun v _ => a v))
      (fun _ => 0) q ha.2
    change follows (fun v => head v (a v)) q at hfollow
    have hroot := firstRoot_eq_of_follows_avoids R (fun v => head v (a v)) hhit q hfollow havoid
    intro v hv
    change v ∈ S ∪ {v | v ∈ q.vertices} at hv
    change (if v ∈ departures q then branchHistoryColor head x seed n h.1
        (historyTrace head (x n) h.2).1 else branchHistoryColor head x seed n h.1 v) = _
    by_cases hvS : v ∈ S
    · have hvdep : v ∉ departures q := fun hd => hfirst.2.2 v hd hvS
      rw [if_neg hvdep]
      exact ih h.1 hfirst.1 ha.1 v hvS
    · have hvq : v ∈ q.vertices := hv.resolve_left hvS
      have hvdep : v ∈ departures q := by
        have hm : v ∈ departures q ++ [(historyTrace head (x n) h.2).1] := by
          simpa only [departures, Path.dropLast_append_end_eq, q] using hvq
        rcases List.mem_append.mp hm with hm | hm
        · exact hm
        · exact (hvS ((List.mem_singleton.mp hm) ▸ hend)).elim
      rw [if_pos hvdep, ih h.1 hfirst.1 ha.1 _ hend, hroot v hvq]

end
end FiniteAvalanches.Wilson.Lattice
