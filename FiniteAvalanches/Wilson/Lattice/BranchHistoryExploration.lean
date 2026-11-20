import FiniteAvalanches.Wilson.Lattice.FiniteBranchHistories

/-! Finite branch histories recover raw Wilson exploration. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V D : Type*} [DecidableEq V]

/-- Raw stack exploration respects concatenation of query lists. -/
theorem rawStackExplore_append (head : V → D → V) (σ : V × ℕ → D)
    (R : Set V) (k : Cursor V) (L M : List V) :
    rawStackExplore head σ R k (L ++ M) =
      (rawStackExplore head σ R k L).bind fun out => rawStackExplore head σ out.1 out.2 M := by
  induction L generalizing R k with
  | nil => rfl
  | cons x xs ih =>
    cases hs : rawStackStep head σ R k x with
    | none => simp only [List.cons_append, rawStackExplore, hs, Option.bind_none]
    | some out =>
      obtain ⟨S, l⟩ := out
      simpa only [List.cons_append, rawStackExplore, hs, Option.bind_some] using ih S l

/-- If each recorded branch reaches its roots before the horizon, the resulting
root set and cursor are exactly those of raw finite Wilson exploration. -/
theorem rawStackExplore_eq_boundedBranchHistory
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N n : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (h : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N) :
    rawStackExplore head σ R k ((List.range n).map x) =
      some (branchHistoryRoots head x R n (boundedBranchHistory head x R k N σ n),
        branchHistoryCursor head x k n (boundedBranchHistory head x R k N σ n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpast : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hs := ih hpast
    let b := boundedBranchHistory head x R k N σ n
    let S := branchHistoryRoots head x R n b
    let c := branchHistoryCursor head x k n b
    have hhit : boundedWordHit head S (x n) c N (readingLetter head (x n) c σ) < N :=
      h n (Nat.lt_succ_self n)
    have hstep := rawStackStep_eq_history_of_boundedHit head S (x n) c N σ hhit
    rw [List.range_succ, List.map_append, rawStackExplore_append, hs]
    simp only [List.map_singleton, rawStackExplore, hstep, Option.bind_some,
      boundedBranchHistory, branchHistoryRoots, branchHistoryCursor, b, S, c]

/-- Bounded branch histories recover the same roots as successful
cycle-popping exploration, and their cursors agree away from those roots. -/
theorem stackExplore_eq_boundedBranchHistory
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N n : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (h : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N)
    (S : Set V) (j : Cursor V)
    (hs : stackExplore head (fun v i => σ (v, i)) R k ((List.range n).map x) = some (S, j)) :
    S = branchHistoryRoots head x R n (boundedBranchHistory head x R k N σ n) ∧
      ∀ v, v ∉ S → j v = branchHistoryCursor head x k n
        (boundedBranchHistory head x R k N σ n) v := by
  obtain ⟨m, hm, hcursor⟩ := rawStackExplore_of_stackExplore head σ R k k
    ((List.range n).map x) S j (fun _ _ => rfl) hs
  rw [rawStackExplore_eq_boundedBranchHistory head x R k N n σ h] at hm
  have he := Option.some.inj hm
  obtain ⟨hS, hm⟩ := Prod.mk.inj he
  refine ⟨hS.symm, ?_⟩
  intro v hv
  exact (hcursor v hv).trans (congrFun hm.symm v)

end
end FiniteAvalanches.Wilson.Lattice
