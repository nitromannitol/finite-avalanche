import FiniteAvalanches.Wilson.Lattice.BranchHistoryExploration

/-! Recovering the cycle-popping cursor from finite branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- The cycle-popping cursor obtained by erasing each recorded branch. -/
def branchHistoryErasedCursor (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (k : Cursor V) : (n : ℕ) → BranchHistory n → Cursor V
  | 0, _ => k
  | n + 1, h => by
    letI : Quiver V := instructionQuiver head
    exact erasedCursor (branchHistoryErasedCursor head x k n h.1)
      (historyTrace head (x n) h.2).2

/-- A recorded first-hit branch gives the exact cycle-popping step, even if
its raw reading cursor differs on the existing roots. -/
theorem stackStep_eq_history_of_boundedHit
    (head : V → FiniteWired.Direction → V) (R : Set V) (x : V)
    (k l : Cursor V) (N : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (hcursor : ∀ v, v ∉ R → k v = l v)
    (h : boundedWordHit head R x l N (readingLetter head x l σ) < N) :
    letI : Quiver V := instructionQuiver head
    let p := stoppedDirectionHistory (boundedWordHit head R x l N) (readingLetter head x l σ)
    stackStep head (fun v i => σ (v, i)) R k x =
      some (historyRoots head x R p, erasedCursor k (historyTrace head x p).2) ∧
      ∀ v, v ∉ historyRoots head x R p →
        erasedCursor k (historyTrace head x p).2 v = historyCursor head x l p v := by
  letI : Quiver V := instructionQuiver head
  let w := readingLetter head x l σ
  let t := boundedWordHit head R x l N w
  let p := stoppedDirectionHistory (boundedWordHit head R x l N) w
  have hw := instructionTrace_eq_read_driver head x l σ
  have hhit : (instructionTrace head (fun v i => σ (v, i)) l x t).1 ∈ R := by
    rw [(hw t).1]
    exact boundedWordHit_mem_of_lt head R x l N w h
  have havoid : ∀ i < t, (instructionTrace head (fun v j => σ (v, j)) l x i).1 ∉ R := by
    intro i hi
    rw [(hw i).1]
    exact boundedWordHit_avoids head R x l N w i hi
  have heq := instructionTrace_eq_until_roots head R x l k σ t
    (fun v hv => (hcursor v hv).symm) havoid
  have hk : ∃ i, (instructionTrace head (fun v j => σ (v, j)) k x i).1 ∈ R :=
    ⟨t, (congrArg Sigma.fst heq) ▸ hhit⟩
  have hfind : Nat.find hk = t := by
    apply Nat.le_antisymm (Nat.find_min' hk ((congrArg Sigma.fst heq) ▸ hhit))
    apply Nat.le_of_not_gt
    intro hi
    have ht := instructionTrace_eq_until_roots head R x l k σ (Nat.find hk)
      (fun v hv => (hcursor v hv).symm) (fun i hi' => havoid i (lt_trans hi' hi))
    exact havoid _ hi ((congrArg Sigma.fst ht).symm ▸ Nat.find_spec hk)
  have hp : historyTrace head x p = instructionTrace head (fun v i => σ (v, i)) l x t :=
    historyTrace_stoppedDirectionHistory head x l (boundedWordHit head R x l N) σ
  have hc := historyCursor_stoppedDirectionHistory head x l (boundedWordHit head R x l N) σ
  have hr := (instructionTrace_eq_readingState head x l σ t).2
  change stackStep head (fun v i => σ (v, i)) R k x =
      some (historyRoots head x R p, erasedCursor k (historyTrace head x p).2) ∧
      ∀ v, v ∉ historyRoots head x R p →
        erasedCursor k (historyTrace head x p).2 v = historyCursor head x l p v
  constructor
  · simp only [stackStep, dif_pos hk]
    rw [hfind, ← heq, ← hp]
    rfl
  · intro v hv
    have hvR : v ∉ R := fun hv' => hv (Or.inl hv')
    have hvp : v ∉ (loopErase (historyTrace head x p).2).vertices := fun hv' => hv (Or.inr hv')
    rw [erasedCursor_eq_consume_of_not_mem k _ v hvp, hc, ← hr, ← hp,
      consume_apply, consume_apply, hcursor v hvR]

/-- Stack exploration respects concatenation of query lists. -/
theorem stackExplore_append (head : V → FiniteWired.Direction → V)
    (σ : V × ℕ → FiniteWired.Direction) (R : Set V) (k : Cursor V)
    (L M : List V) :
    stackExplore head (fun v i => σ (v, i)) R k (L ++ M) =
      (stackExplore head (fun v i => σ (v, i)) R k L).bind
        fun out => stackExplore head (fun v i => σ (v, i)) out.1 out.2 M := by
  induction L generalizing R k with
  | nil => rfl
  | cons x xs ih =>
    cases hs : stackStep head (fun v i => σ (v, i)) R k x with
    | none => simp only [List.cons_append, stackExplore, hs, Option.bind_none]
    | some out =>
      obtain ⟨S, l⟩ := out
      simpa only [List.cons_append, stackExplore, hs, Option.bind_some] using ih S l

/-- Successful finite branch histories recover the exact cycle-popping cursor
and agree with the raw cursor away from the attached roots. -/
theorem stackExplore_eq_historyErasedCursor
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N n : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (h : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N) :
    let a := boundedBranchHistory head x R k N σ n
    stackExplore head (fun v i => σ (v, i)) R k ((List.range n).map x) =
      some (branchHistoryRoots head x R n a, branchHistoryErasedCursor head x k n a) ∧
    ∀ v, v ∉ branchHistoryRoots head x R n a →
      branchHistoryErasedCursor head x k n a v = branchHistoryCursor head x k n a v := by
  induction n with
  | zero => exact ⟨rfl, fun _ _ => rfl⟩
  | succ n ih =>
    have hpast : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    obtain ⟨hexplore, hcursor⟩ := ih hpast
    let a := boundedBranchHistory head x R k N σ n
    let S := branchHistoryRoots head x R n a
    let c := branchHistoryCursor head x k n a
    let j := branchHistoryErasedCursor head x k n a
    have hhit : boundedWordHit head S (x n) c N (readingLetter head (x n) c σ) < N :=
      h n (Nat.lt_succ_self n)
    have hs := stackStep_eq_history_of_boundedHit head S (x n) j c N σ hcursor hhit
    constructor
    · rw [List.range_succ, List.map_append, stackExplore_append, hexplore]
      simp only [List.map_singleton, stackExplore, hs.1, Option.bind_some,
        boundedBranchHistory, branchHistoryRoots, branchHistoryErasedCursor, a, S, c, j]
    · simpa only [boundedBranchHistory, branchHistoryRoots, branchHistoryCursor,
        branchHistoryErasedCursor, a, S, c, j] using hs.2

end
end FiniteAvalanches.Wilson.Lattice
