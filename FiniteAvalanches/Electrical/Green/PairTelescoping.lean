import FiniteAvalanches.Electrical.Green.FiniteTelescoping

/-! The literal four-term boundary pair expression and its finite triangular sum. -/
namespace FiniteAvalanches.Electrical
open scoped BigOperators

/-- The expanded Green expression at two boundary-edge indices. -/
def boundaryPairKernel {m : ℕ} (G : Fin (m+1) → Fin (m+1) → ℝ) (i j : Fin m) : ℝ :=
  G 0 i.castSucc*(G i.succ j.castSucc-G i.succ j.succ)
  -G 0 i.succ*(G i.castSucc j.castSucc-G i.castSucc j.succ)
  -G 0 j.castSucc*(G i.castSucc j.succ-G i.succ j.succ)
  +G 0 j.succ*(G i.castSucc j.castSucc-G i.succ j.castSucc)

/-- Ordered pairs retain adjacency and endpoint coincidences. -/
def boundaryPairSum {m : ℕ} (G : Fin (m+1) → Fin (m+1) → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then boundaryPairKernel G i j else 0

private theorem suffix_green {m : ℕ} (G : Fin (m+1) → Fin (m+1) → ℝ)
    (r : Fin (m+1)) (i : Fin m) :
    (∑ j : Fin m, if i.val < j.val then G r j.castSucc-G r j.succ else 0) =
      G r i.succ-G r (Fin.last m) := by
  simpa only [Fin.val_succ,Nat.succ_le_iff] using sum_suffix_sub m (G r) i.succ

private theorem prefix_green {m : ℕ} (G : Fin (m+1) → Fin (m+1) → ℝ)
    (r : Fin (m+1)) (j : Fin m) :
    (∑ i : Fin m, if i.val < j.val then G i.castSucc r-G i.succ r else 0) =
      G 0 r-G j.castSucc r := by
  exact sum_prefix_sub m (fun k => G k r) j.castSucc

private theorem sum_first_two {m : ℕ} (G : Fin (m+1) → Fin (m+1) → ℝ)
    (hg : ∀ r, G r (Fin.last m) = 0) (i : Fin m) :
    (∑ j : Fin m, if i.val < j.val then
      G 0 i.castSucc*(G i.succ j.castSucc-G i.succ j.succ)
        -G 0 i.succ*(G i.castSucc j.castSucc-G i.castSucc j.succ) else 0) =
      G 0 i.castSucc*G i.succ i.succ-G 0 i.succ*G i.castSucc i.succ := by
  have heq : (∑ j : Fin m, if i.val < j.val then
      G 0 i.castSucc*(G i.succ j.castSucc-G i.succ j.succ)
        -G 0 i.succ*(G i.castSucc j.castSucc-G i.castSucc j.succ) else 0) =
      G 0 i.castSucc*(∑ j : Fin m, if i.val < j.val then G i.succ j.castSucc-G i.succ j.succ else 0)
        -G 0 i.succ*(∑ j : Fin m, if i.val < j.val then G i.castSucc j.castSucc-G i.castSucc j.succ else 0) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [heq,suffix_green,suffix_green,hg,hg,sub_zero,sub_zero]

private theorem sum_last_two {m : ℕ} (G : Fin (m+1) → Fin (m+1) → ℝ) (j : Fin m) :
    (∑ i : Fin m, if i.val < j.val then
      -G 0 j.castSucc*(G i.castSucc j.succ-G i.succ j.succ)
        +G 0 j.succ*(G i.castSucc j.castSucc-G i.succ j.castSucc) else 0) =
      G 0 j.castSucc*G j.castSucc j.succ-G 0 j.succ*G j.castSucc j.castSucc := by
  have heq : (∑ i : Fin m, if i.val < j.val then
      -G 0 j.castSucc*(G i.castSucc j.succ-G i.succ j.succ)
        +G 0 j.succ*(G i.castSucc j.castSucc-G i.succ j.castSucc) else 0) =
      -G 0 j.castSucc*(∑ i : Fin m, if i.val < j.val then G i.castSucc j.succ-G i.succ j.succ else 0)
        +G 0 j.succ*(∑ i : Fin m, if i.val < j.val then G i.castSucc j.castSucc-G i.succ j.castSucc else 0) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [heq,prefix_green,prefix_green]
  ring

/-- Both triangular telescopes give the two source single sums before diagonal rearrangement. -/
theorem boundaryPairSum_eq_edge_sum {m : ℕ} (G : Fin (m+1) → Fin (m+1) → ℝ)
    (hg : ∀ r, G r (Fin.last m) = 0) :
    boundaryPairSum G = ∑ i : Fin m,
      (G 0 i.castSucc*G i.succ i.succ-G 0 i.succ*G i.castSucc i.castSucc+
        (G 0 i.castSucc-G 0 i.succ)*G i.castSucc i.succ) := by
  let A := fun i j : Fin m => G 0 i.castSucc*(G i.succ j.castSucc-G i.succ j.succ)
    -G 0 i.succ*(G i.castSucc j.castSucc-G i.castSucc j.succ)
  let B := fun i j : Fin m => -G 0 j.castSucc*(G i.castSucc j.succ-G i.succ j.succ)
    +G 0 j.succ*(G i.castSucc j.castSucc-G i.succ j.castSucc)
  have hsplit : boundaryPairSum G =
      (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then A i j else 0) +
      (∑ j : Fin m, ∑ i : Fin m, if i.val < j.val then B i j else 0) := by
    rw [Finset.sum_comm (f := fun j i : Fin m => if i.val < j.val then B i j else 0)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [A,B]
    split_ifs
    · dsimp only [boundaryPairKernel]
      ring
    · ring
  rw [hsplit]
  dsimp only [A,B]
  simp_rw [sum_first_two G hg,sum_last_two G]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact source pair sum. Symmetry and the grounded last row give the last column. -/
theorem boundaryPairSum_eq {m : ℕ} (G : Fin (m+1) → Fin (m+1) → ℝ)
    (hs : ∀ i j, G i j = G j i) (hg : ∀ j, G (Fin.last m) j = 0) :
    boundaryPairSum G =
      (∑ i : Fin m, (G 0 i.castSucc-G 0 i.succ)*
        (G i.castSucc i.castSucc+G i.succ i.succ+G i.castSucc i.succ))-(G 0 0)^2 := by
  have hc : ∀ i, G i (Fin.last m) = 0 := fun i => (hs i _).trans (hg i)
  have ht := sum_sub_succ m (fun i => G 0 i*G i i)
  simp only [hc,zero_mul,sub_zero] at ht
  rw [boundaryPairSum_eq_edge_sum G hc,pow_two,← ht,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end FiniteAvalanches.Electrical
