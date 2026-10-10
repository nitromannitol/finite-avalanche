import FiniteAvalanches.Electrical.Green.PairTelescoping
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The deterministic boundary pair bound from Green positivity and nonnegative edge drops. -/
namespace FiniteAvalanches.Electrical
open scoped BigOperators Classical

/-- Testing a positive semidefinite matrix on the difference of two coordinate vectors. -/
theorem two_mul_entry_le_diag_add {V : Type*} [Fintype V]
    (G : Matrix V V ℝ) (hG : G.PosSemidef) (i j : V) : 2*G i j ≤ G i i+G j j := by
  have h := hG.dotProduct_mulVec_nonneg (Pi.single i 1-Pi.single j 1)
  simp only [star_trivial,Matrix.mulVec_sub,sub_dotProduct,Matrix.mulVec_single_one,
    single_dotProduct,one_mul,Pi.sub_apply] at h
  have hs : G j i = G i j := by simpa only [star_trivial] using hG.1.apply i j
  change 0 ≤ G i i-G i j-(G j i-G j j) at h
  rw [hs] at h
  linarith only [h]

/-- No probabilities are inputs: this is the algebraic bound on the expanded pair kernel. -/
theorem boundaryPairSum_le {m : ℕ} (G : Fin (m+1) → Fin (m+1) → ℝ)
    (hs : ∀ i j, G i j = G j i) (hg : ∀ j, G (Fin.last m) j = 0)
    (hp : ∀ i : Fin m, 0 ≤ G 0 i.castSucc-G 0 i.succ)
    (hdiag : ∀ i : Fin m, 2*G i.castSucc i.succ ≤ G i.castSucc i.castSucc+G i.succ i.succ) :
    boundaryPairSum G ≤ (G 0 0)^2/2 + (3/2 : ℝ)*∑ i : Fin m,
      (G 0 i.castSucc-G 0 i.succ)*
        ((G i.castSucc i.castSucc-G 0 i.castSucc)+(G i.succ i.succ-G 0 i.succ)) := by
  have hc : ∀ i, G i (Fin.last m) = 0 := fun i => (hs i _).trans (hg i)
  have hsq : (∑ i : Fin m, (G 0 i.castSucc-G 0 i.succ)*(G 0 i.castSucc+G 0 i.succ)) = (G 0 0)^2 := by
    calc
      _ = ∑ i : Fin m, ((G 0 i.castSucc)^2-(G 0 i.succ)^2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (G 0 0)^2 := by
        have h := sum_sub_succ m (fun i => (G 0 i)^2)
        simpa only [hc,zero_pow (by decide : (2 : ℕ) ≠ 0),sub_zero] using h
  have hsum : (∑ i : Fin m, (G 0 i.castSucc-G 0 i.succ)*
        (G i.castSucc i.castSucc+G i.succ i.succ+G i.castSucc i.succ)) ≤
      (3/2 : ℝ)*∑ i : Fin m, (G 0 i.castSucc-G 0 i.succ)*(G i.castSucc i.castSucc+G i.succ i.succ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (hdiag i) (hp i)
    nlinarith only [h]
  have hsplit : (∑ i : Fin m, (G 0 i.castSucc-G 0 i.succ)*(G i.castSucc i.castSucc+G i.succ i.succ)) =
      (∑ i : Fin m, (G 0 i.castSucc-G 0 i.succ)*(G 0 i.castSucc+G 0 i.succ)) +
      ∑ i : Fin m, (G 0 i.castSucc-G 0 i.succ)*
        ((G i.castSucc i.castSucc-G 0 i.castSucc)+(G i.succ i.succ-G 0 i.succ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [boundaryPairSum_eq G hs hg]
  calc
    _ ≤ (3/2 : ℝ)*(∑ i : Fin m, (G 0 i.castSucc-G 0 i.succ)*(G i.castSucc i.castSucc+G i.succ i.succ))-(G 0 0)^2 :=
      sub_le_sub_right hsum _
    _ = _ := by rw [hsplit,hsq]; ring

/-- Positive semidefiniteness supplies the exact adjacent-entry inequality used by the source. -/
theorem boundaryPairSum_le_of_posSemidef {m : ℕ} (G : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (hG : G.PosSemidef) (hg : ∀ j, G (Fin.last m) j = 0)
    (hp : ∀ i : Fin m, 0 ≤ G 0 i.castSucc-G 0 i.succ) :
    boundaryPairSum G ≤ (G 0 0)^2/2 + (3/2 : ℝ)*∑ i : Fin m,
      (G 0 i.castSucc-G 0 i.succ)*
        ((G i.castSucc i.castSucc-G 0 i.castSucc)+(G i.succ i.succ-G 0 i.succ)) := by
  apply boundaryPairSum_le G (fun i j => ?_) hg hp
    (fun i => two_mul_entry_le_diag_add G hG i.castSucc i.succ)
  simpa only [star_trivial] using hG.1.apply j i

end FiniteAvalanches.Electrical
