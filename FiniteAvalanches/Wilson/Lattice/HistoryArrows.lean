import FiniteAvalanches.Wilson.Lattice.HistorySelected

/-! Finite Wilson histories determine the arrows attached to their roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Each recorded branch ends at a previously attached root. -/
def BranchHistory.EndsInRoots (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (R : Set V) : (n : ℕ) → BranchHistory n → Prop
  | 0, _ => True
  | n + 1, h => BranchHistory.EndsInRoots head x R n h.1 ∧
      (historyTrace head (x n) h.2).1 ∈ branchHistoryRoots head x R n h.1

/-- Successful bounded histories have genuine root endpoints. -/
theorem branchHistory_endsInRoots_of_hits
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N n : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (h : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N) :
    BranchHistory.EndsInRoots head x R n (boundedBranchHistory head x R k N σ n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hpast : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    let a := boundedBranchHistory head x R k N σ n
    let S := branchHistoryRoots head x R n a
    let c := branchHistoryCursor head x k n a
    let w := readingLetter head (x n) c σ
    let t := boundedWordHit head S (x n) c N w
    let p := stoppedDirectionHistory (boundedWordHit head S (x n) c N) w
    have hhit : t < N := h n (Nat.lt_succ_self n)
    have ht := historyTrace_stoppedDirectionHistory head (x n) c (boundedWordHit head S (x n) c N) σ
    have hw := instructionTrace_eq_read_driver head (x n) c σ t
    change BranchHistory.EndsInRoots head x R n a ∧ (historyTrace head (x n) p).1 ∈ S
    refine ⟨ih hpast, ?_⟩
    rw [ht, hw.1]
    exact boundedWordHit_mem_of_lt head S (x n) c N w hhit

/-- An assignment realizes a history when it contains all retained branch arrows. -/
def BranchHistory.Realizes (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (a : V → FiniteWired.Direction) (n : ℕ) (h : BranchHistory n) : Prop :=
  BranchHistory.Selected head x (fun p => a p.1) (fun _ => 0) n h

omit [DecidableEq V] in
/-- Selection of a path depends only on the selected instructions. -/
theorem selected_constant_top (head : V → FiniteWired.Direction → V)
    (σ : V × ℕ → FiniteWired.Direction) (k : Cursor V) {x y : V}
    (p : letI : Quiver V := instructionQuiver head; Path x y)
    (h : letI : Quiver V := instructionQuiver head
      selected (instructionArrowStacks head (fun v i => σ (v, i))) k p) :
    letI : Quiver V := instructionQuiver head
    selected (instructionArrowStacks head (fun v _ => σ (v, k v))) (fun _ => 0) p := by
  letI : Quiver V := instructionQuiver head
  induction p with
  | nil => trivial
  | cons p e ih => exact ⟨ih h.1, h.2⟩

/-- The selected top instructions realize every selected branch. -/
theorem BranchHistory.Selected.top
    (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (σ : V × ℕ → FiniteWired.Direction) (n : ℕ) (a : BranchHistory n)
    (k : Cursor V) (h : BranchHistory.Selected head x σ k n a) :
    BranchHistory.Realizes head x (fun v => σ (v, k v)) n a := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change BranchHistory.Selected head x σ k n a.1 ∧ _ at h
    change BranchHistory.Selected head x (fun p => σ (p.1, k p.1)) (fun _ => 0) n a.1 ∧ _
    exact ⟨ih a.1 h.1, selected_constant_top head σ k _ h.2⟩

/-- The cycle-popping output realizes all branches in a successful history. -/
theorem branchHistory_top_realizes_of_hits
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N n : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (h : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N) :
    let a := boundedBranchHistory head x R k N σ n
    let j := branchHistoryErasedCursor head x k n a
    BranchHistory.Realizes head x (fun v => σ (v, j v)) n a := by
  exact BranchHistory.Selected.top head x σ n _ _
    (branchHistory_selected_of_hits head x R k N n σ h)

omit [DecidableEq V] in
/-- Two assignments selecting the same path agree at each departure. -/
theorem selected_directions_eq_of_mem_departures
    (head : V → FiniteWired.Direction → V) (a b : V → FiniteWired.Direction)
    {x y : V} (p : letI : Quiver V := instructionQuiver head; Path x y)
    (ha : letI : Quiver V := instructionQuiver head
      selected (instructionArrowStacks head (fun v _ => a v)) (fun _ => 0) p)
    (hb : letI : Quiver V := instructionQuiver head
      selected (instructionArrowStacks head (fun v _ => b v)) (fun _ => 0) p)
    {v : V} (hv : letI : Quiver V := instructionQuiver head; v ∈ departures p) : a v = b v := by
  letI : Quiver V := instructionQuiver head
  induction p with
  | nil => exact False.elim (List.not_mem_nil hv)
  | @cons u w p e ih =>
    rw [departures_cons] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ih ha.1 hb.1 hv
    · have he : v = u := List.mem_singleton.mp hv
      subst v
      have h := ha.2.trans hb.2.symm
      exact congrArg (fun z : Σ y : V, u ⟶ y => z.2.val) h

/-- Root-ending histories determine all realized directions at attached
vertices outside the initial root set. -/
theorem BranchHistory.Realizes.eq_of_mem_roots
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (n : ℕ) (h : BranchHistory n) (a b : V → FiniteWired.Direction)
    (hend : BranchHistory.EndsInRoots head x R n h)
    (ha : BranchHistory.Realizes head x a n h)
    (hb : BranchHistory.Realizes head x b n h)
    {v : V} (hv : v ∈ branchHistoryRoots head x R n h) (hvR : v ∉ R) : a v = b v := by
  letI : Quiver V := instructionQuiver head
  induction n with
  | zero => exact (hvR hv).elim
  | succ n ih =>
    change BranchHistory.EndsInRoots head x R n h.1 ∧ _ at hend
    change BranchHistory.Realizes head x a n h.1 ∧ _ at ha
    change BranchHistory.Realizes head x b n h.1 ∧ _ at hb
    change v ∈ branchHistoryRoots head x R n h.1 ∪
      {v | v ∈ (loopErase (historyTrace head (x n) h.2).2).vertices} at hv
    rcases hv with hv | hv
    · exact ih h.1 hend.1 ha.1 hb.1 hv
    · change v ∈ (loopErase (historyTrace head (x n) h.2).2).vertices at hv
      by_cases hvold : v ∈ branchHistoryRoots head x R n h.1
      · exact ih h.1 hend.1 ha.1 hb.1 hvold
      · have hdep : v ∈ departures (loopErase (historyTrace head (x n) h.2).2) := by
          have hm : v ∈ departures (loopErase (historyTrace head (x n) h.2).2) ++
              [(historyTrace head (x n) h.2).1] := by
            simpa only [departures, Path.dropLast_append_end_eq] using hv
          rcases List.mem_append.mp hm with hm | hm
          · exact hm
          · exact (hvold ((List.mem_singleton.mp hm) ▸ hend.2)).elim
        exact selected_directions_eq_of_mem_departures head a b _ ha.2 hb.2 hdep

end
end FiniteAvalanches.Wilson.Lattice
