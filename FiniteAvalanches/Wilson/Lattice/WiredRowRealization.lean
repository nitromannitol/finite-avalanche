import FiniteAvalanches.Wilson.Lattice.WiredObservationSampler

/-! Almost-sure wired realizability of finite independent-row histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A finite wired row history has a finite common horizon and a cycle-free
arrow assignment realizing its retained branches. -/
def wiredRowRealizationEvent (R : RootPair) (B : ℕ) (x : ℕ → FiniteWired.Vertex B)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) : Set (ℕ → WalkDriver) :=
  {rows | ∃ N, BranchHistory.HitsBefore N n
      (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n) ∧
    ∃ a : GoodArrows (wiredRoots R B).val (wiredHead B),
      BranchHistory.Realizes (wiredHead B) x a.val n
        (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n)}

/-- Finite wired realizability is a measurable row event. -/
theorem measurableSet_wiredRowRealizationEvent (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    MeasurableSet (wiredRowRealizationEvent R B x k n) := by
  let P : ℕ → BranchHistory n → Prop := fun N h => BranchHistory.HitsBefore N n h ∧
    ∃ a : GoodArrows (wiredRoots R B).val (wiredHead B), BranchHistory.Realizes (wiredHead B) x a.val n h
  have he : wiredRowRealizationEvent R B x k n = ⋃ N : ℕ,
      {rows | P N (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n)} := by
    ext rows
    simp only [wiredRowRealizationEvent, Set.mem_setOf_eq, Set.mem_iUnion, P]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  exact measurableSet_of_countable_fibers
    (fun rows => rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n)
    (fun a => measurableSet_rowBranchHistory_eq (wiredHead B) x (wiredRoots R B).val k N n
      (fun i (rows : ℕ → WalkDriver) => rows i) (fun i => measurable_pi_apply i) a) (P N)

/-- Independent uniform rows produce a realizable finite wired history almost surely. -/
theorem wilsonRows_ae_wiredRowRealization (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, rows ∈ wiredRowRealizationEvent R B x k n := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_wiredRowRealizationEvent R B x k n)).mpr
  have hm := wilsonRows_wiredForest_eq_of_prefix_determines R B x k n Set.univ
    (by intro h hh a b ha hb; exact Iff.rfl)
  have he : {rows | ∃ N,
      BranchHistory.HitsBefore N n
        (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n) ∧
      BranchHistory.WiredForestEvent R B x n Set.univ
        (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n)} =
      wiredRowRealizationEvent R B x k n := by
    ext rows
    simp only [wiredRowRealizationEvent, BranchHistory.WiredForestEvent, Set.mem_setOf_eq,
      Set.mem_univ, and_true]
  rw [he] at hm
  simpa only [measure_univ] using hm

/-- Two successful finite row histories coincide regardless of their horizons. -/
theorem rowBranchHistory_eq_of_two_hits {V : Type*} [DecidableEq V]
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N M n : ℕ) (rows : ℕ → WalkDriver)
    (hN : ∀ i < n, (rowBranchHistory head x R k N rows (i + 1)).2.1 < N)
    (hM : ∀ i < n, (rowBranchHistory head x R k M rows (i + 1)).2.1 < M) :
    rowBranchHistory head x R k N rows n = rowBranchHistory head x R k M rows n := by
  let K := max N M
  have hNK : N ≤ K := le_max_left _ _
  have hMK : M ≤ K := le_max_right _ _
  have h1 := rowBranchHistory_eq_of_hits head x R k N K n rows hNK hN
  have h2 := rowBranchHistory_eq_of_hits head x R k M K n rows hMK hM
  exact h1.symm.trans h2

end
end FiniteAvalanches.Wilson.Lattice
