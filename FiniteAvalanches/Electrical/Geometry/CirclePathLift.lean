import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.IntermediateValue

open Set unitInterval

namespace FiniteAvalanches.Electrical.StatementGeometry

/-- A simple circle path lifts to increasing or decreasing real angles within one turn. -/
theorem simple_circle_path_angles (f : C(I, Circle)) (hf : Function.Injective f) :
    ∃ θ : C(I, ℝ), (∀ t, Circle.exp (θ t) = f t) ∧
      (StrictMono θ ∨ StrictAnti θ) ∧ |θ 1 - θ 0| < 2 * Real.pi := by
  obtain ⟨θ, hθ, _⟩ := Circle.isCoveringMap_exp.exists_path_lifts f
    (Complex.arg (f 0)) (Circle.exp_arg (f 0)).symm
  have heq (t : I) : Circle.exp (θ t) = f t := congrFun hθ t
  have hinj : Function.Injective θ := fun s t h => hf ((heq s).symm.trans
    ((congrArg Circle.exp h).trans (heq t)))
  refine ⟨θ, heq, θ.continuous.strictMono_of_inj hinj, ?_⟩
  have hupper : θ 1 - θ 0 < 2 * Real.pi := by
    by_contra hn
    have hle : θ 0 + 2 * Real.pi ≤ θ 1 := by linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) 1 θ.continuous
      (show θ 0 + 2 * Real.pi ∈ Set.Icc (θ 0) (θ 1) from
        ⟨by linarith [Real.pi_pos], hle⟩)
    have hf0 : f t = f 0 := by
      rw [← heq t, ht, Circle.periodic_exp, heq]
    have ht0 := hf hf0
    rw [ht0] at ht
    linarith [Real.pi_pos]
  have hlower : -(2 * Real.pi) < θ 1 - θ 0 := by
    by_contra hn
    have hle : θ 1 + 2 * Real.pi ≤ θ 0 := by linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ (1 : I) 0 θ.continuous
      (show θ 1 + 2 * Real.pi ∈ Set.Icc (θ 1) (θ 0) from
        ⟨by linarith [Real.pi_pos], hle⟩)
    have hf1 : f t = f 1 := by
      rw [← heq t, ht, Circle.periodic_exp, heq]
    have ht1 := hf hf1
    rw [ht1] at ht
    linarith [Real.pi_pos]
  exact abs_lt.mpr ⟨hlower, hupper⟩

#print axioms simple_circle_path_angles
end FiniteAvalanches.Electrical.StatementGeometry
