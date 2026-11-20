import FiniteAvalanches.Wilson.Lattice.BranchHistoryLaw

/-! Finite Wilson branch histories driven by independent walk rows. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Record each bounded Wilson branch from its own direction row. -/
def rowBranchHistory (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (R : Set V) (k : Cursor V) (N : ℕ) (rows : ℕ → WalkDriver) :
    (n : ℕ) → BranchHistory n
  | 0 => ()
  | n + 1 =>
    let h := rowBranchHistory head x R k N rows n
    let c := branchHistoryCursor head x k n h
    let S := branchHistoryRoots head x R n h
    (h, stoppedDirectionHistory (boundedWordHit head S (x n) c N) (rows n))

/-- The first `n` row histories depend only on the first `n` rows. -/
theorem rowBranchHistory_eq_of_prefix (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N n : ℕ)
    (rows rows' : ℕ → WalkDriver) (h : ∀ i < n, rows' i = rows i) :
    rowBranchHistory head x R k N rows' n = rowBranchHistory head x R k N rows n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    change (rowBranchHistory head x R k N rows' n,
      stoppedDirectionHistory (boundedWordHit head
        (branchHistoryRoots head x R n (rowBranchHistory head x R k N rows' n)) (x n)
        (branchHistoryCursor head x k n (rowBranchHistory head x R k N rows' n)) N) (rows' n)) =
      (rowBranchHistory head x R k N rows n,
      stoppedDirectionHistory (boundedWordHit head
        (branchHistoryRoots head x R n (rowBranchHistory head x R k N rows n)) (x n)
        (branchHistoryCursor head x k n (rowBranchHistory head x R k N rows n)) N) (rows n))
    rw [hp, h n (Nat.lt_succ_self n)]

/-- Exact finite row histories are measurable whenever the row drivers are. -/
theorem measurableSet_rowBranchHistory_eq {Ω : Type*} [MeasurableSpace Ω]
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N n : ℕ) (rows : ℕ → Ω → WalkDriver)
    (hm : ∀ i, Measurable (rows i)) (a : BranchHistory n) :
    MeasurableSet {ω | rowBranchHistory head x R k N (fun i => rows i ω) n = a} := by
  induction n with
  | zero =>
    have he : {ω | rowBranchHistory head x R k N (fun i => rows i ω) 0 = a} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      change Unit at a
      cases a
      rfl
    rw [he]
    exact MeasurableSet.univ
  | succ n ih =>
    rcases a with ⟨b, p⟩
    let t := boundedWordHit head (branchHistoryRoots head x R n b) (x n)
      (branchHistoryCursor head x k n b) N
    let A : Set WalkDriver := {w | stoppedDirectionHistory t w = p}
    have hA : MeasurableSet A := measurableSet_stoppedDirectionHistory_eq t
      (boundedWordHit_stable head (branchHistoryRoots head x R n b) (x n)
        (branchHistoryCursor head x k n b) N) p
    have he : {ω | rowBranchHistory head x R k N (fun i => rows i ω) (n + 1) = (b, p)} =
        {ω | rowBranchHistory head x R k N (fun i => rows i ω) n = b} ∩ (rows n) ⁻¹' A := by
      ext ω
      change ((rowBranchHistory head x R k N (fun i => rows i ω) n,
        stoppedDirectionHistory (boundedWordHit head
          (branchHistoryRoots head x R n (rowBranchHistory head x R k N (fun i => rows i ω) n)) (x n)
          (branchHistoryCursor head x k n (rowBranchHistory head x R k N (fun i => rows i ω) n)) N)
          (rows n ω)) : BranchHistory n × DirectionHistory) = (b, p) ↔
        rowBranchHistory head x R k N (fun i => rows i ω) n = b ∧ rows n ω ∈ A
      simp only [Prod.mk.injEq, A, Set.mem_setOf_eq, t]
      constructor
      · rintro ⟨hb, hp⟩
        exact ⟨hb, by simpa only [hb] using hp⟩
      · rintro ⟨hb, hp⟩
        exact ⟨hb, by simpa only [hb] using hp⟩
    rw [he]
    exact (ih b).inter ((hm n) hA)

end
end FiniteAvalanches.Wilson.Lattice
