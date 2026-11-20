import FiniteAvalanches.Wilson.Lattice.BranchHistoryEvents
import FiniteAvalanches.Wilson.Lattice.BranchHistoryExploration

/-! Stability of finite Wilson branch histories as the time horizon grows. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Once a first root hit occurs before one horizon, every larger horizon
records the same hitting time. -/
theorem boundedWordHit_eq_of_hit (head : V → FiniteWired.Direction → V) (R : Set V)
    (x : V) (k : Cursor V) (N M : ℕ) (w : WalkDriver) (hNM : N ≤ M)
    (hN : boundedWordHit head R x k N w < N) :
    boundedWordHit head R x k M w = boundedWordHit head R x k N w := by
  let t := boundedWordHit head R x k N w
  let u := boundedWordHit head R x k M w
  have ht : (wordState head x k w t).1 ∈ R := boundedWordHit_mem_of_lt head R x k N w hN
  have hu : u ≤ t := by
    apply Nat.le_of_not_gt
    intro hlt
    exact boundedWordHit_avoids head R x k M w t hlt ht
  have htu : t ≤ u := by
    apply Nat.le_of_not_gt
    intro hlt
    have hroot : (wordState head x k w u).1 ∈ R :=
      boundedWordHit_mem_of_lt head R x k M w (lt_of_lt_of_le (lt_trans hlt hN) hNM)
    exact boundedWordHit_avoids head R x k N w u hlt hroot
  exact Nat.le_antisymm hu htu

/-- A finite genuine root hit is recorded strictly before some finite horizon. -/
theorem exists_boundedWordHit_lt (head : V → FiniteWired.Direction → V) (R : Set V)
    (x : V) (k : Cursor V) (w : WalkDriver)
    (h : ∃ n, (wordState head x k w n).1 ∈ R) :
    ∃ N, boundedWordHit head R x k N w < N := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, ?_⟩
  have hex : ∃ i < n + 1, (wordState head x k w i).1 ∈ R := ⟨n, Nat.lt_succ_self n, hn⟩
  simpa only [boundedWordHit, dif_pos hex] using (Nat.find_spec hex).1

/-- If all recorded branches hit before `N`, increasing the horizon leaves the
entire ordered branch history unchanged. -/
theorem boundedBranchHistory_eq_of_hits (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N M n : ℕ)
    (σ : V × ℕ → FiniteWired.Direction) (hNM : N ≤ M)
    (h : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N) :
    boundedBranchHistory head x R k M σ n = boundedBranchHistory head x R k N σ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpast : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hs := ih hpast
    let a := boundedBranchHistory head x R k N σ n
    let S := branchHistoryRoots head x R n a
    let c := branchHistoryCursor head x k n a
    let w := readingLetter head (x n) c σ
    have hhit : boundedWordHit head S (x n) c N w < N := h n (Nat.lt_succ_self n)
    have htime := boundedWordHit_eq_of_hit head S (x n) c N M w hNM hhit
    change (boundedBranchHistory head x R k M σ n,
      stoppedDirectionHistory (boundedWordHit head
        (branchHistoryRoots head x R n (boundedBranchHistory head x R k M σ n)) (x n)
        (branchHistoryCursor head x k n (boundedBranchHistory head x R k M σ n)) M)
        (readingLetter head (x n) (branchHistoryCursor head x k n
          (boundedBranchHistory head x R k M σ n)) σ)) =
      (a, stoppedDirectionHistory (boundedWordHit head S (x n) c N) w)
    rw [hs]
    change (a, stoppedDirectionHistory (boundedWordHit head S (x n) c M) w) =
      (a, stoppedDirectionHistory (boundedWordHit head S (x n) c N) w)
    congr 1
    change (⟨boundedWordHit head S (x n) c M w, fun i => w i.val⟩ : DirectionHistory) =
      ⟨boundedWordHit head S (x n) c N w, fun i => w i.val⟩
    exact congrArg (fun t : ℕ => (⟨t, fun i : Fin t => w i.val⟩ : DirectionHistory)) htime

/-- Any successful raw finite exploration is fully captured before a sufficiently
large common finite horizon. -/
theorem exists_horizon_of_rawStackExplore (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (n : ℕ)
    (σ : V × ℕ → FiniteWired.Direction) (S : Set V) (l : Cursor V)
    (hs : rawStackExplore head σ R k ((List.range n).map x) = some (S, l)) :
    ∃ N, ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N := by
  induction n generalizing S l with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, rawStackExplore_append] at hs
    cases hprev : rawStackExplore head σ R k ((List.range n).map x) with
    | none => simp only [hprev, Option.bind_none] at hs; cases hs
    | some out =>
      obtain ⟨T, c⟩ := out
      have hstep : rawStackStep head σ T c (x n) = some (S, l) := by
        simp only [hprev, Option.bind_some, List.map_singleton, rawStackExplore] at hs
        obtain ⟨out, hout, hres⟩ := Option.bind_eq_some_iff.mp hs
        obtain ⟨U, m⟩ := out
        simp only [Option.some.injEq, Prod.mk.injEq] at hres
        obtain ⟨rfl, rfl⟩ := hres
        exact hout
      obtain ⟨N, hN⟩ := ih T c hprev
      have he := rawStackExplore_eq_boundedBranchHistory head x R k N n σ hN
      rw [hprev, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hT, hc⟩ := he
      let a := boundedBranchHistory head x R k N σ n
      let S' := branchHistoryRoots head x R n a
      let c' := branchHistoryCursor head x k n a
      have hstep' : rawStackStep head σ S' c' (x n) = some (S, l) := by
        simpa only [S', c', a, ← hT, ← hc] using hstep
      have hhit : ∃ i, (instructionTrace head (fun v j => σ (v, j)) c' (x n) i).1 ∈ S' := by
        by_contra hn
        simp only [rawStackStep, dif_neg hn] at hstep'
        cases hstep'
      let w := readingLetter head (x n) c' σ
      have hword : ∃ i, (wordState head (x n) c' w i).1 ∈ S' := by
        obtain ⟨i, hi⟩ := hhit
        exact ⟨i, (instructionTrace_eq_read_driver head (x n) c' σ i).1 ▸ hi⟩
      obtain ⟨M, hM⟩ := exists_boundedWordHit_lt head S' (x n) c' w hword
      let K := max N M
      have hNK : N ≤ K := le_max_left _ _
      have hMK : M ≤ K := le_max_right _ _
      have hpast (i : ℕ) (hi : i < n) :
          (boundedBranchHistory head x R k K σ (i + 1)).2.1 < K := by
        have hsmall : ∀ j < i + 1,
            (boundedBranchHistory head x R k N σ (j + 1)).2.1 < N :=
          fun j hj => hN j (lt_of_lt_of_le hj (Nat.succ_le_of_lt hi))
        rw [boundedBranchHistory_eq_of_hits head x R k N K (i + 1) σ hNK hsmall]
        exact lt_of_lt_of_le (hN i hi) hNK
      have ha : boundedBranchHistory head x R k K σ n = a :=
        boundedBranchHistory_eq_of_hits head x R k N K n σ hNK hN
      have hlast : (boundedBranchHistory head x R k K σ (n + 1)).2.1 < K := by
        change boundedWordHit head
          (branchHistoryRoots head x R n (boundedBranchHistory head x R k K σ n)) (x n)
          (branchHistoryCursor head x k n (boundedBranchHistory head x R k K σ n)) K
          (readingLetter head (x n)
            (branchHistoryCursor head x k n (boundedBranchHistory head x R k K σ n)) σ) < K
        rw [ha]
        change boundedWordHit head S' (x n) c' K w < K
        rw [boundedWordHit_eq_of_hit head S' (x n) c' M K w hMK hM]
        exact lt_of_lt_of_le hM hMK
      refine ⟨K, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hpast i hi
      · exact hlast

/-- Every successful cycle-popping exploration is represented by finite
histories at a sufficiently large common horizon. -/
theorem exists_horizon_of_stackExplore (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (n : ℕ)
    (σ : V × ℕ → FiniteWired.Direction) (S : Set V) (l : Cursor V)
    (hs : stackExplore head (fun v i => σ (v, i)) R k ((List.range n).map x) = some (S, l)) :
    ∃ N, ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N := by
  obtain ⟨m, hm, _⟩ := rawStackExplore_of_stackExplore head σ R k k
    ((List.range n).map x) S l (fun _ _ => rfl) hs
  exact exists_horizon_of_rawStackExplore head x R k n σ S m hm

end
end FiniteAvalanches.Wilson.Lattice
