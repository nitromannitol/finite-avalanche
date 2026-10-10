import FiniteAvalanches.Electrical.ForestColor.Enumeration
import FiniteAvalanches.Electrical.Dirichlet

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ForestColor
open Trees ForestGramCounting
open scoped Classical BigOperators Matrix
noncomputable section
variable {n : ℕ} {E : Type} [Fintype E] (G : Multigraph (Fin (n + 2)) E)

/-- The all-minors positive Laplacian has exactly the source electrical action. -/
theorem fullCopiedLaplacian_mulVec (f : Fin (n + 2) → ℝ) (x : Fin (n + 2)) :
    (fullCopiedLaplacian G *ᵥ f) x = laplacian G.left G.right f x := by
  simp only [Matrix.mulVec, dotProduct, fullCopiedLaplacian, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold laplacian
  apply Finset.sum_congr rfl
  intro e _
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  have hs : (∑ y : Fin (n + 2),
      ((if y = G.left e then (1 : ℝ) else 0) - (if y = G.right e then 1 else 0)) * f y) =
      f (G.left e) - f (G.right e) := by
    simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
    simp
  rw [hs]
  clear hs
  by_cases ha : x = G.left e <;> by_cases hb : x = G.right e <;> simp_all [eq_comm]

end
end FiniteAvalanches.Electrical.ForestColor
