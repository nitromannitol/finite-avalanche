import FiniteAvalanches.Wilson.Lattice.HistoryRootward
import FiniteAvalanches.Wilson.Lattice.WiredPrefixForestLaw

/-! Colors determined by finite wired Wilson branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Every query in a recorded branch history belongs to its attached roots. -/
theorem mem_branchHistoryRoots_of_query {V : Type*} [DecidableEq V]
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (n : ℕ) (h : BranchHistory n) {i : ℕ} (hi : i < n) :
    x i ∈ branchHistoryRoots head x R n h := by
  letI : Quiver V := instructionQuiver head
  induction n with
  | zero => omega
  | succ n ih =>
    change x i ∈ branchHistoryRoots head x R n h.1 ∪
      {v | v ∈ (FiniteAvalanches.Wilson.loopErase (historyTrace head (x n) h.2).2).vertices}
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inl (ih h.1 hi)
    · exact Or.inr (Quiver.Path.start_mem_vertices _)

/-- A wired arrow forest assigns the color of the first root on each orbit. -/
theorem finiteColors_arrowForest_eq_true_iff (R : RootPair) (B : ℕ)
    (a : GoodArrows (wiredRoots R B).val (wiredHead B)) (v : FiniteWired.Vertex B) :
    let f := fun v => wiredHead B v (a.val v)
    let h := GoodArrows.reaches_root (wiredRoots R B).val (wiredHead B) a.val a.property
    finiteColors R B (wiredArrowForest R B a) v = true ↔
      firstRoot (wiredRoots R B).val f h v ∈ wiredOne R B := by
  let f := fun v => wiredHead B v (a.val v)
  let h := GoodArrows.reaches_root (wiredRoots R B).val (wiredHead B) a.val a.property
  let r := firstRoot (wiredRoots R B).val f h v
  have hr : r ∈ (wiredRoots R B).val := firstRoot_mem _ _ _ v
  have hreach : (WiredTrees.graph B).reaches (wiredArrowCopies R B a) v r := by
    apply reaches_iterate_before_root (WiredTrees.graph B) (wiredArrowCopies R B a)
      (wiredRoots R B).val f (wiredArrowCopies_step R B a) v (Nat.find (h v))
    intro i hi
    exact Nat.find_min (h v) hi
  change finiteColors R B (wiredArrowForest R B a) v = true ↔ r ∈ wiredOne R B
  simp only [finiteColors, decide_eq_true_eq]
  constructor
  · rintro ⟨u, hu, hvu⟩
    obtain ⟨s, _, _, hs⟩ := (wiredArrowForest R B a).property.2 v
    have he : u = r := (hs u (Or.inr hu) hvu).trans (hs r hr hreach).symm
    exact he ▸ hu
  · intro hrOne
    exact ⟨r, hrOne, hreach⟩

/-- Realizations of the same root-ending history give equal colors at every
attached vertex. -/
theorem BranchHistory.Realizes.wiredColor_eq (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (n : ℕ) (h : BranchHistory n)
    (a b : GoodArrows (wiredRoots R B).val (wiredHead B))
    (hend : BranchHistory.EndsInRoots (wiredHead B) x (wiredRoots R B).val n h)
    (ha : BranchHistory.Realizes (wiredHead B) x a.val n h)
    (hb : BranchHistory.Realizes (wiredHead B) x b.val n h)
    {v : FiniteWired.Vertex B} (hv : v ∈ branchHistoryRoots (wiredHead B) x (wiredRoots R B).val n h) :
    finiteColors R B (wiredArrowForest R B a) v = finiteColors R B (wiredArrowForest R B b) v := by
  have he := BranchHistory.Realizes.firstRoot_eq (wiredHead B) x (wiredRoots R B).val n h
    a.val b.val hend ha hb
    (GoodArrows.reaches_root _ _ _ a.property) (GoodArrows.reaches_root _ _ _ b.property) hv
  have ht : finiteColors R B (wiredArrowForest R B a) v = true ↔
      finiteColors R B (wiredArrowForest R B b) v = true := by
    have hA := finiteColors_arrowForest_eq_true_iff R B a v
    have hB := finiteColors_arrowForest_eq_true_iff R B b v
    dsimp only at hA hB
    rw [hA, hB, he]
  cases hca : finiteColors R B (wiredArrowForest R B a) v <;>
    cases hcb : finiteColors R B (wiredArrowForest R B b) v <;> simp_all

/-- The finite wired color cylinder at queried vertices is determined by the
corresponding root-ending Wilson branch history. -/
theorem wiredColorCylinder_determined_by_history (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (n : ℕ) (h : BranchHistory n)
    (D : Finset (FiniteWired.Vertex B)) (p : FiniteWired.Vertex B → Bool)
    (hD : ∀ v ∈ D, ∃ i < n, x i = v)
    (hend : BranchHistory.EndsInRoots (wiredHead B) x (wiredRoots R B).val n h)
    (a b : GoodArrows (wiredRoots R B).val (wiredHead B))
    (ha : BranchHistory.Realizes (wiredHead B) x a.val n h)
    (hb : BranchHistory.Realizes (wiredHead B) x b.val n h) :
    (∀ v ∈ D, finiteColors R B (wiredArrowForest R B a) v = p v) ↔
      (∀ v ∈ D, finiteColors R B (wiredArrowForest R B b) v = p v) := by
  have he (v : FiniteWired.Vertex B) (hv : v ∈ D) :
      finiteColors R B (wiredArrowForest R B a) v = finiteColors R B (wiredArrowForest R B b) v := by
    obtain ⟨i, hi, rfl⟩ := hD v hv
    exact BranchHistory.Realizes.wiredColor_eq R B x n h a b hend ha hb
      (mem_branchHistoryRoots_of_query (wiredHead B) x (wiredRoots R B).val n h hi)
  constructor <;> intro hc v hv
  · rw [← he v hv]
    exact hc v hv
  · rw [he v hv]
    exact hc v hv

end
end FiniteAvalanches.Wilson.Lattice
