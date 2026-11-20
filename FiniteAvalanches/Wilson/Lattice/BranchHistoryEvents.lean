import FiniteAvalanches.Wilson.Lattice.RowBranchHistoryLaw

/-! Equality in law of finite stack and independent-row branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile Function
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Exact finite stack branch histories are measurable. -/
theorem measurableSet_boundedBranchHistory_eq (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N n : ℕ) (a : BranchHistory n) :
    MeasurableSet {σ | boundedBranchHistory head x R k N σ n = a} := by
  induction n with
  | zero =>
    change Unit at a
    cases a
    simp only [boundedBranchHistory, Set.setOf_true]
    exact MeasurableSet.univ
  | succ n ih =>
    rcases a with ⟨b, p⟩
    let t := boundedWordHit head (branchHistoryRoots head x R n b) (x n)
      (branchHistoryCursor head x k n b) N
    let A : Set WalkDriver := {w | stoppedDirectionHistory t w = p}
    have hA : MeasurableSet A := measurableSet_stoppedDirectionHistory_eq t
      (boundedWordHit_stable head (branchHistoryRoots head x R n b) (x n)
        (branchHistoryCursor head x k n b) N) p
    have he : {σ | boundedBranchHistory head x R k N σ (n + 1) = (b, p)} =
        {σ | boundedBranchHistory head x R k N σ n = b} ∩
          (fun σ => readingLetter head (x n) (branchHistoryCursor head x k n b) σ) ⁻¹' A := by
      ext σ
      change ((boundedBranchHistory head x R k N σ n,
        stoppedDirectionHistory (boundedWordHit head
          (branchHistoryRoots head x R n (boundedBranchHistory head x R k N σ n)) (x n)
          (branchHistoryCursor head x k n (boundedBranchHistory head x R k N σ n)) N)
          (readingLetter head (x n)
            (branchHistoryCursor head x k n (boundedBranchHistory head x R k N σ n)) σ)) :
          BranchHistory n × DirectionHistory) = (b, p) ↔
        boundedBranchHistory head x R k N σ n = b ∧
          readingLetter head (x n) (branchHistoryCursor head x k n b) σ ∈ A
      simp only [Prod.mk.injEq, A, Set.mem_setOf_eq, t]
      constructor
      · rintro ⟨hb, hp⟩
        exact ⟨hb, by simpa only [hb] using hp⟩
      · rintro ⟨hb, hp⟩
        exact ⟨hb, by simpa only [hb] using hp⟩
    rw [he]
    exact (ih b).inter ((measurable_readingDriver V head (x n) (branchHistoryCursor head x k n b)) hA)

/-- Any event of the bounded finite branch history has the same probability
under vertex stacks and under independent walk rows. -/
theorem directionStackLaw_branchHistory_event_eq_wilsonRows
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N n : ℕ) (P : BranchHistory n → Prop) :
    directionStackLaw V {σ | P (boundedBranchHistory head x R k N σ n)} =
      wilsonRows {rows | P (rowBranchHistory head x R k N rows n)} := by
  let I := {a : BranchHistory n // P a}
  let E : I → Set (V × ℕ → FiniteWired.Direction) := fun a =>
    {σ | boundedBranchHistory head x R k N σ n = a.val}
  let F : I → Set (ℕ → WalkDriver) := fun a =>
    {rows | rowBranchHistory head x R k N rows n = a.val}
  have hE : ∀ a, MeasurableSet (E a) := fun a =>
    measurableSet_boundedBranchHistory_eq head x R k N n a.val
  have hF : ∀ a, MeasurableSet (F a) := fun a =>
    measurableSet_rowBranchHistory_eq head x R k N n (fun i (rows : ℕ → WalkDriver) => rows i)
      (fun i => measurable_pi_apply i) a.val
  have hdE : Pairwise (Disjoint on E) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro σ ha hb
    exact hab (Subtype.ext (ha.symm.trans hb))
  have hdF : Pairwise (Disjoint on F) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro rows ha hb
    exact hab (Subtype.ext (ha.symm.trans hb))
  have he : {σ | P (boundedBranchHistory head x R k N σ n)} = ⋃ a : I, E a := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
    constructor
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
    · rintro ⟨a, ha⟩
      rw [ha]
      exact a.property
  have hf : {rows | P (rowBranchHistory head x R k N rows n)} = ⋃ a : I, F a := by
    ext rows
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, F]
    constructor
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
    · rintro ⟨a, ha⟩
      rw [ha]
      exact a.property
  rw [he, hf, measure_iUnion hdE hE, measure_iUnion hdF hF]
  exact tsum_congr fun a => directionStackLaw_branchHistory_eq_wilsonRows head x R k N n a.val

end
end FiniteAvalanches.Wilson.Lattice
