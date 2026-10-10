import FiniteAvalanches.Electrical.Ratio.Green

/-! Unit-voltage conductance and unit-current Green resistance use the same copied energy. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Ratio
open StatementGeometry Source
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- Dividing the characterized unit voltage by its positive flux gives the unit-current solve. -/
theorem groundedGreen_diagonal_eq_conductance_inv (J : CopiedGraph V E) (s t : V)
    (hne : s ≠ t) (hc : (supportGraph J.left J.right).Preconnected) :
    groundedGreen J.left J.right s hc t t = (effectiveConductance J s t hne hc)⁻¹ := by
  let C := effectiveConductance J s t hne hc
  have hC : C ≠ 0 := ne_of_gt (effectiveConductance_pos J s t hne hc)
  obtain ⟨hs, ht, hh⟩ := voltage_spec J s t hne hc
  have hsolve : C⁻¹ • voltage J s t hc = groundedGreen J.left J.right s hc t := by
    apply groundedPoisson_eq J.left J.right s hc (fun z => if z = t then 1 else 0)
    constructor
    · simp only [Pi.smul_apply, smul_eq_mul, hs, mul_zero]
    · intro x hxs
      rw [laplacian_smul]
      by_cases hxt : x = t
      · rw [hxt, if_pos rfl, ← effectiveConductance_eq_flux J s t hne hc]
        exact inv_mul_cancel₀ hC
      · rw [hh x hxs hxt, if_neg hxt, mul_zero]
  rw [← hsolve]
  simp only [Pi.smul_apply, smul_eq_mul, ht, mul_one]
  rfl

/-- Conductance is the reciprocal of the actual unit-current Green diagonal. -/
theorem effectiveConductance_eq_green_inv (J : CopiedGraph V E) (s t : V)
    (hne : s ≠ t) (hc : (supportGraph J.left J.right).Preconnected) :
    effectiveConductance J s t hne hc = (groundedGreen J.left J.right s hc t t)⁻¹ := by
  rw [groundedGreen_diagonal_eq_conductance_inv, inv_inv]

/-- Unit effective conductance is the full copied tree count over the full two-root count. -/
theorem effectiveConductance_eq_count_ratio (J : CopiedGraph V E) (s t : V)
    (hne : s ≠ t) (hc : (supportGraph J.left J.right).Preconnected) :
    effectiveConductance J s t hne hc =
      (Nat.card J.SpanningTree : ℝ) / (Nat.card (J.TwoRootForest s t) : ℝ) := by
  have hswap : J.TwoRootForest t s = J.TwoRootForest s t := by
    unfold CopiedGraph.TwoRootForest
    rw [Set.pair_comm]
  rw [effectiveConductance_eq_green_inv,
    groundedGreen_diagonal_eq_count_ratio J s t hc hne.symm, inv_div, hswap]

end
end FiniteAvalanches.Electrical.Ratio
