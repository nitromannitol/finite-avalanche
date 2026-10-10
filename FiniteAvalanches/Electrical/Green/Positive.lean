import FiniteAvalanches.Electrical.Green.Grounded

/-! Positivity of the actual grounded Green kernel by copied Dirichlet energy. -/
namespace FiniteAvalanches.Electrical
open scoped BigOperators Classical
variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- The copied Laplacian commutes with a finite sum of real functions. -/
theorem laplacian_sum_univ {K : Type*} [Fintype K] (a b : E → V) (f : K → V → ℝ) (x : V) :
    laplacian a b (fun y => ∑ k, f k y) x = ∑ k, laplacian a b (f k) x := by
  let L : (V → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun g => laplacian a b g x
      map_add' := fun g h => laplacian_add a b g h x
      map_smul' := fun r g => laplacian_smul a b r g x }
  have h := map_sum L f Finset.univ
  change laplacian a b (∑ k : K, f k) x = ∑ k : K, laplacian a b (f k) x at h
  have heq : (∑ k : K, f k) = (fun y => ∑ k : K, f k y) := by
    funext y
    simp only [Finset.sum_apply]
  rw [heq] at h
  exact h

/-- Every charge vector's Green quadratic form is an actual once-counted copied-edge energy. -/
theorem groundedGreen_quadratic_eq_energy (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (c : V → ℝ) :
    (∑ x, ∑ y, c x*groundedGreen a b v hc x y*c y) =
      energy a b (fun y => ∑ x, c x*groundedGreen a b v hc x y) := by
  let H := fun y => ∑ x, c x*groundedGreen a b v hc x y
  have hground : H v = 0 := by simp [H,groundedGreen_ground]
  have hforce (y : V) (hy : y ≠ v) : laplacian a b H y = c y := by
    rw [laplacian_sum_univ]
    calc
      _ = ∑ x, c x*(if y = x then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        change laplacian a b (c x • groundedGreen a b v hc x) y = _
        rw [laplacian_smul,groundedGreen_laplacian a b v hc x y hy]
      _ = c y := by simp
  rw [energy_eq_incidence_sum]
  calc
    _ = ∑ y, H y*c y := by
      rw [Finset.sum_comm]
      simp only [H,Finset.sum_mul]
    _ = ∑ y, H y*laplacian a b H y := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y = v
      · subst y; rw [hground,zero_mul,zero_mul]
      · rw [hforce y hy]

/-- Full positive semidefiniteness, including the zero ground row and column. -/
theorem groundedGreen_posSemidef (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) : Matrix.PosSemidef (groundedGreen a b v hc : Matrix V V ℝ) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro x y
    simpa only [star_trivial] using groundedGreen_symm a b v hc y x
  · intro c
    have h := energy_nonneg a b (fun y => ∑ x, c x*groundedGreen a b v hc x y)
    rw [← groundedGreen_quadratic_eq_energy] at h
    simpa only [star_trivial,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc] using h

/-- The kernel represents the unique Poisson solve on its complete original vertex carrier. -/
theorem groundedPoisson_eq_green_sum (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (c : V → ℝ) :
    groundedPoisson a b v hc c = fun y => ∑ x, c x*groundedGreen a b v hc x y := by
  symm
  apply groundedPoisson_eq
  constructor
  · simp [groundedGreen_ground]
  · intro y hy
    rw [laplacian_sum_univ]
    calc
      _ = ∑ x, c x*(if y = x then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        change laplacian a b (c x • groundedGreen a b v hc x) y = _
        rw [laplacian_smul,groundedGreen_laplacian a b v hc x y hy]
      _ = c y := by simp

end FiniteAvalanches.Electrical
