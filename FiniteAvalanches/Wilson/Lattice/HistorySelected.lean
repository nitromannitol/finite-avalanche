import FiniteAvalanches.Wilson.Lattice.HistoryErasedCursor

/-! The retained arrows of finite Wilson branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- A first-hit history records exactly the arrows selected after cycle popping. -/
theorem historyTrace_selected_of_boundedHit
    (head : V → FiniteWired.Direction → V) (R : Set V) (x : V)
    (k l : Cursor V) (N : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (hcursor : ∀ v, v ∉ R → k v = l v)
    (h : boundedWordHit head R x l N (readingLetter head x l σ) < N) :
    letI : Quiver V := instructionQuiver head
    let p := stoppedDirectionHistory (boundedWordHit head R x l N) (readingLetter head x l σ)
    selected (instructionArrowStacks head (fun v i => σ (v, i)))
      (erasedCursor k (historyTrace head x p).2) (loopErase (historyTrace head x p).2) := by
  letI : Quiver V := instructionQuiver head
  let w := readingLetter head x l σ
  let t := boundedWordHit head R x l N w
  let p := stoppedDirectionHistory (boundedWordHit head R x l N) w
  have hw := instructionTrace_eq_read_driver head x l σ
  have havoid : ∀ i < t, (instructionTrace head (fun v j => σ (v, j)) l x i).1 ∉ R := by
    intro i hi
    rw [(hw i).1]
    exact boundedWordHit_avoids head R x l N w i hi
  have hdep := instructionTrace_departures_avoid R head (fun v i => σ (v, i)) l x t havoid
  have hs := (instructionTrace_erasure R head (fun v i => σ (v, i)) l x t hdep).2.1
  have hp : historyTrace head x p = instructionTrace head (fun v i => σ (v, i)) l x t :=
    historyTrace_stoppedDirectionHistory head x l (boundedWordHit head R x l N) σ
  change selected (instructionArrowStacks head (fun v i => σ (v, i)))
    (erasedCursor k (historyTrace head x p).2) (loopErase (historyTrace head x p).2)
  rw [hp]
  apply selected_congr _ _ hs
  intro v hv
  have hvR : v ∉ R := hdep v ((loopErase_vertices_sublist _).subset (List.mem_of_mem_dropLast hv) |>
    fun hv' => by
      have hh : v ∈ departures (instructionTrace head (fun v i => σ (v, i)) l x t).2 ++
          [(instructionTrace head (fun v i => σ (v, i)) l x t).1] := by
        simpa only [departures, Path.dropLast_append_end_eq] using hv'
      rcases List.mem_append.mp hh with hh | hh
      · exact hh
      · have he := List.mem_singleton.mp hh
        subst v
        exact False.elim (by
          have hn := loopErase_vertices_nodup (instructionTrace head (fun v i => σ (v, i)) l x t).2
          have hend : (instructionTrace head (fun v i => σ (v, i)) l x t).1 ∉ departures (loopErase (instructionTrace head (fun v i => σ (v, i)) l x t).2) := by
            have hnd := (Path.dropLast_append_end_eq (loopErase (instructionTrace head (fun v i => σ (v, i)) l x t).2)) ▸ hn
            exact fun hvd => (List.nodup_append.mp hnd).2.2 _ hvd _ (List.mem_singleton_self _) rfl
          exact hend hv))
  simp only [erasedCursor, consume_apply, hcursor v hvR]

/-- Every retained branch in a history selects its original instructions. -/
def BranchHistory.Selected (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (σ : V × ℕ → FiniteWired.Direction) (k : Cursor V) :
    (n : ℕ) → BranchHistory n → Prop
  | 0, _ => True
  | n + 1, h => by
    letI : Quiver V := instructionQuiver head
    exact BranchHistory.Selected head x σ k n h.1 ∧
      selected (instructionArrowStacks head (fun v i => σ (v, i))) k
        (loopErase (historyTrace head (x n) h.2).2)

/-- Cursor changes away from the recorded roots preserve all recorded arrows. -/
theorem BranchHistory.Selected.congr (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (σ : V × ℕ → FiniteWired.Direction)
    (k l : Cursor V) (n : ℕ) (h : BranchHistory n)
    (hs : BranchHistory.Selected head x σ k n h)
    (he : ∀ v ∈ branchHistoryRoots head x R n h, k v = l v) :
    BranchHistory.Selected head x σ l n h := by
  letI : Quiver V := instructionQuiver head
  induction n with
  | zero => trivial
  | succ n ih =>
    change BranchHistory.Selected head x σ l n h.1 ∧
      selected (instructionArrowStacks head (fun v i => σ (v, i))) l
        (loopErase (historyTrace head (x n) h.2).2)
    have hs' : BranchHistory.Selected head x σ k n h.1 ∧
      selected (instructionArrowStacks head (fun v i => σ (v, i))) k
        (loopErase (historyTrace head (x n) h.2).2) := hs
    constructor
    · apply ih h.1 hs'.1
      intro v hv
      exact he v (Or.inl hv)
    · apply selected_congr _ _ hs'.2
      intro v hv
      exact he v (Or.inr (List.mem_of_mem_dropLast hv))

/-- Once all branches have hit, the cycle-popping cursor selects every
arrow retained in their finite recorded histories. -/
theorem branchHistory_selected_of_hits
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N n : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (h : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N) :
    let a := boundedBranchHistory head x R k N σ n
    BranchHistory.Selected head x σ (branchHistoryErasedCursor head x k n a) n a := by
  letI : Quiver V := instructionQuiver head
  induction n with
  | zero => trivial
  | succ n ih =>
    have hpast : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    let a := boundedBranchHistory head x R k N σ n
    let S := branchHistoryRoots head x R n a
    let c := branchHistoryCursor head x k n a
    let j := branchHistoryErasedCursor head x k n a
    let p := stoppedDirectionHistory (boundedWordHit head S (x n) c N)
      (readingLetter head (x n) c σ)
    let q := erasedCursor j (historyTrace head (x n) p).2
    have hhit : boundedWordHit head S (x n) c N (readingLetter head (x n) c σ) < N :=
      h n (Nat.lt_succ_self n)
    have hcursor := (stackExplore_eq_historyErasedCursor head x R k N n σ hpast).2
    have hstep := (stackStep_eq_history_of_boundedHit head S (x n) j c N σ hcursor hhit).1
    have hrun := (stackStep_of_some S head (fun v i => σ (v, i)) j (x n)
      (historyRoots head (x n) S p) q hstep).2.2
    have hselected := historyTrace_selected_of_boundedHit head S (x n) j c N σ hcursor hhit
    change BranchHistory.Selected head x σ q n a ∧
      selected (instructionArrowStacks head (fun v i => σ (v, i))) q
        (loopErase (historyTrace head (x n) p).2)
    refine ⟨?_, hselected⟩
    apply BranchHistory.Selected.congr head x R σ j q n a (ih hpast)
    intro v hv
    exact (pop_run_root_cursor S head (fun v i => σ (v, i)) hrun hv).symm

end
end FiniteAvalanches.Wilson.Lattice
