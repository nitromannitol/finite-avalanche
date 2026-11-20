import FiniteAvalanches.Wilson.Lattice.RowBranchHistory
import FiniteAvalanches.Wilson.Lattice.Sampler

/-! Comparison of stack-driven and independently row-driven branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory ProbabilityTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- The first `n` row histories are independent of the next complete row. -/
theorem wilsonRows_branchHistory_indep (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N n : ℕ)
    (a : BranchHistory n) (A : Set WalkDriver) (hA : MeasurableSet A) :
    wilsonRows {rows | rowBranchHistory head x R k N rows n = a ∧ rows n ∈ A} =
      wilsonRows {rows | rowBranchHistory head x R k N rows n = a} * walkLaw A := by
  let S := Finset.range n
  let T : Finset ℕ := {n}
  have hdis : Disjoint S T := by simp only [S, T, Finset.disjoint_singleton_right,
    Finset.mem_range, lt_self_iff_false, not_false_eq_true]
  let f : (ℕ → WalkDriver) → (S → WalkDriver) := fun rows i => rows i.val
  let g : (ℕ → WalkDriver) → (T → WalkDriver) := fun rows i => rows i.val
  let extend : (S → WalkDriver) → ℕ → WalkDriver := fun p i =>
    if hi : i < n then p ⟨i, Finset.mem_range.mpr hi⟩ else fun _ => (0, false)
  let E : Set (S → WalkDriver) := {p | rowBranchHistory head x R k N (extend p) n = a}
  let B : Set (T → WalkDriver) := {p | p ⟨n, Finset.mem_singleton_self n⟩ ∈ A}
  have hm : ∀ i, Measurable (fun p : S → WalkDriver => extend p i) := by
    intro i
    by_cases hi : i < n
    · simpa only [extend, dif_pos hi] using
        (measurable_pi_apply (⟨i, Finset.mem_range.mpr hi⟩ : S))
    · simpa only [extend, dif_neg hi] using
        (measurable_const : Measurable (fun _ : S → WalkDriver =>
          ((fun _ => (0, false)) : WalkDriver)))
  have hE : MeasurableSet E := measurableSet_rowBranchHistory_eq head x R k N n
    (fun i p => extend p i) hm a
  have hB : MeasurableSet B :=
    (show Measurable (fun p : T → WalkDriver => p ⟨n, Finset.mem_singleton_self n⟩) from
      measurable_pi_apply _) hA
  have hf : f ⁻¹' E = {rows | rowBranchHistory head x R k N rows n = a} := by
    ext rows
    simp only [Set.mem_preimage, E, Set.mem_setOf_eq]
    have he := rowBranchHistory_eq_of_prefix head x R k N n rows (extend (f rows))
      (fun i hi => by simp only [extend, dif_pos hi, f])
    rw [he]
  have hg : g ⁻¹' B = {rows | rows n ∈ A} := by
    ext rows
    simp only [Set.mem_preimage, B, Set.mem_setOf_eq, g]
  have hind : iIndepFun (fun i : ℕ => fun rows : ℕ → WalkDriver => rows i) wilsonRows := by
    exact iIndepFun_infinitePi (X := fun (_ : ℕ) (w : WalkDriver) => w) (fun _ => measurable_id)
  have hprod := (hind.indepFun_finset S T hdis (fun i => measurable_pi_apply i))
    |>.measure_inter_preimage_eq_mul E B hE hB
  rw [hf, hg] at hprod
  have hrow : wilsonRows {rows | rows n ∈ A} = walkLaw A := by
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => walkLaw) n).measure_preimage hA.nullMeasurableSet
  rw [hrow] at hprod
  exact hprod

/-- Row-driven finite branch histories satisfy the usual transition formula. -/
theorem wilsonRows_rowBranchHistory_succ (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N n : ℕ)
    (a : BranchHistory n) (p : DirectionHistory) :
    wilsonRows {rows | rowBranchHistory head x R k N rows (n + 1) = (a, p)} =
      wilsonRows {rows | rowBranchHistory head x R k N rows n = a} *
        walkLaw {w | stoppedDirectionHistory
          (boundedWordHit head (branchHistoryRoots head x R n a) (x n)
            (branchHistoryCursor head x k n a) N) w = p} := by
  let t := boundedWordHit head (branchHistoryRoots head x R n a) (x n)
    (branchHistoryCursor head x k n a) N
  let A : Set WalkDriver := {w | stoppedDirectionHistory t w = p}
  have hA : MeasurableSet A := measurableSet_stoppedDirectionHistory_eq t
    (boundedWordHit_stable head (branchHistoryRoots head x R n a) (x n)
      (branchHistoryCursor head x k n a) N) p
  have he : {rows | rowBranchHistory head x R k N rows (n + 1) = (a, p)} =
      {rows | rowBranchHistory head x R k N rows n = a ∧ rows n ∈ A} := by
    ext rows
    change ((rowBranchHistory head x R k N rows n,
      stoppedDirectionHistory (boundedWordHit head
        (branchHistoryRoots head x R n (rowBranchHistory head x R k N rows n)) (x n)
        (branchHistoryCursor head x k n (rowBranchHistory head x R k N rows n)) N) (rows n)) :
        BranchHistory n × DirectionHistory) = (a, p) ↔
      rowBranchHistory head x R k N rows n = a ∧ rows n ∈ A
    simp only [Prod.mk.injEq, A, Set.mem_setOf_eq, t]
    constructor
    · rintro ⟨ha, hp⟩
      exact ⟨ha, by simpa only [ha] using hp⟩
    · rintro ⟨ha, hp⟩
      exact ⟨ha, by simpa only [ha] using hp⟩
  rw [he]
  exact wilsonRows_branchHistory_indep head x R k N n a A hA

/-- Bounded Wilson branch histories read from vertex stacks and from independent
walk rows have exactly the same distribution. -/
theorem directionStackLaw_branchHistory_eq_wilsonRows [Fintype V]
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N n : ℕ) (a : BranchHistory n) :
    directionStackLaw V {σ | boundedBranchHistory head x R k N σ n = a} =
      wilsonRows {rows | rowBranchHistory head x R k N rows n = a} := by
  induction n with
  | zero =>
    change Unit at a
    cases a
    simp only [boundedBranchHistory, rowBranchHistory, Set.setOf_true, measure_univ]
  | succ n ih =>
    rcases a with ⟨a, p⟩
    rw [directionStackLaw_boundedBranchHistory_succ, wilsonRows_rowBranchHistory_succ]
    rw [ih a]

end
end FiniteAvalanches.Wilson.Lattice
