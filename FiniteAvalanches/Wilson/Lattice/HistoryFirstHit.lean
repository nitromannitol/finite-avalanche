import FiniteAvalanches.Wilson.CyclePopping.ErasureDepartures
import FiniteAvalanches.Wilson.Lattice.RowBranchHorizon
import FiniteAvalanches.Wilson.Lattice.HistoryArrows

/-! First-hit conditions for recorded finite Wilson branches. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- A finite word trace departs from exactly its positions before the endpoint. -/
theorem wordTrace_departures (head : V → FiniteWired.Direction → V)
    (x : V) (w : WalkDriver) :
    letI : Quiver V := instructionQuiver head
    ∀ n, departures (wordTrace head x w n).2 =
      (List.range n).map (fun i => (wordTrace head x w i).1) := by
  letI : Quiver V := instructionQuiver head
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change departures ((wordTrace head x w n).2.cons _) = _
    rw [departures_cons, ih, List.range_succ, List.map_append]
    rfl

/-- A stopped word records its full trace and all its loop-erased departures
avoid the root set when the recorded hit is the first one. -/
theorem historyTrace_firstHit_of_boundedHit (head : V → FiniteWired.Direction → V)
    (R : Set V) (x : V) (k : Cursor V) (N : ℕ) (w : WalkDriver)
    (h : boundedWordHit head R x k N w < N) :
    letI : Quiver V := instructionQuiver head
    let t := boundedWordHit head R x k N w
    let p := stoppedDirectionHistory (fun _ => t) w
    (historyTrace head x p).1 ∈ R ∧
      ∀ v ∈ departures (loopErase (historyTrace head x p).2), v ∉ R := by
  letI : Quiver V := instructionQuiver head
  let t := boundedWordHit head R x k N w
  let p := stoppedDirectionHistory (fun _ => t) w
  have hp : ∀ i < t, p.extend i = w i := by
    intro i hi
    simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi]
  have ht : historyTrace head x p = wordTrace head x w t :=
    wordTrace_eq_of_prefix head x w p.extend t hp
  change (historyTrace head x p).1 ∈ R ∧
    ∀ v ∈ departures (loopErase (historyTrace head x p).2), v ∉ R
  rw [ht]
  constructor
  · rw [wordTrace_fst_eq_wordState head x k w]
    exact boundedWordHit_mem_of_lt head R x k N w h
  · intro v hv
    have hv' := departures_loopErase_subset (wordTrace head x w t).2 v hv
    rw [wordTrace_departures head x w t] at hv'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv'
    rw [wordTrace_fst_eq_wordState head x k w]
    exact boundedWordHit_avoids head R x k N w i (List.mem_range.mp hi)

/-- Each recorded branch first meets the roots already attached by its
predecessors. -/
def BranchHistory.FirstHits (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (R : Set V) : (n : ℕ) → BranchHistory n → Prop
  | 0, _ => True
  | n + 1, h => by
    letI : Quiver V := instructionQuiver head
    let S := branchHistoryRoots head x R n h.1
    let p := historyTrace head (x n) h.2
    exact BranchHistory.FirstHits head x R n h.1 ∧ p.1 ∈ S ∧
      ∀ v ∈ departures (loopErase p.2), v ∉ S

/-- First-hit histories in particular have endpoints at previously attached roots. -/
theorem BranchHistory.FirstHits.endsInRoots (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (n : ℕ) (h : BranchHistory n)
    (hh : BranchHistory.FirstHits head x R n h) : BranchHistory.EndsInRoots head x R n h := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih h.1 hh.1, hh.2.1⟩

/-- Successful bounded independent-row histories satisfy the first-hit
conditions at every recorded branch. -/
theorem rowBranchHistory_firstHits_of_hits (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N n : ℕ) (rows : ℕ → WalkDriver)
    (h : ∀ i < n, (rowBranchHistory head x R k N rows (i + 1)).2.1 < N) :
    BranchHistory.FirstHits head x R n (rowBranchHistory head x R k N rows n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hpast : ∀ i < n, (rowBranchHistory head x R k N rows (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    let a := rowBranchHistory head x R k N rows n
    let S := branchHistoryRoots head x R n a
    let c := branchHistoryCursor head x k n a
    let t := boundedWordHit head S (x n) c N (rows n)
    have ht : t < N := h n (Nat.lt_succ_self n)
    have hlast := historyTrace_firstHit_of_boundedHit head S (x n) c N (rows n) ht
    change BranchHistory.FirstHits head x R n a ∧ _
    exact ⟨ih hpast, hlast⟩

end
end FiniteAvalanches.Wilson.Lattice
