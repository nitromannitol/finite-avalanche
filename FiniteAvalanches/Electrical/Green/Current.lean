import FiniteAvalanches.Electrical.Green.Grounded
import FiniteAvalanches.Electrical.Response

/-! Unit injection and extraction for the actual grounded Green voltage. -/
namespace FiniteAvalanches.Electrical
open scoped BigOperators Classical
variable {V E : Type*} [Fintype V] [Fintype E]

/-- The grounded vertex extracts exactly one unit when the injection vertex is distinct. -/
theorem groundedGreen_laplacian_ground (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (u : V) (hu : u ≠ v) :
    laplacian a b (groundedGreen a b v hc u) v = -1 := by
  have h : (∑ x, (laplacian a b (groundedGreen a b v hc u) x-(if x = u then (1 : ℝ) else 0))) =
      laplacian a b (groundedGreen a b v hc u) v := by
    rw [Finset.sum_eq_single v]
    · rw [if_neg hu.symm,sub_zero]
    · intro x _ hx
      rw [groundedGreen_laplacian a b v hc u x hx,sub_self]
    · simp
  rw [Finset.sum_sub_distrib,sum_laplacian_eq_zero] at h
  simp at h
  exact h.symm

end FiniteAvalanches.Electrical
