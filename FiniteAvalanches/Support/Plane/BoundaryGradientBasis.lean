import FiniteAvalanches.Electrical.Plane.Incidence
import Mathlib.LinearAlgebra.StdBasis

/-!
# Face-boundary gradients on vertex indicators

The universal vanishing of a dual boundary of primal gradients is equivalent
to vanishing on the indicator of each original vertex.
-/

namespace FiniteAvalanches.Electrical.Plane

open scoped Classical

/-- The copied gradient as a linear map on vertex functions. -/
noncomputable def copyGradientMap {V E : Type*} (a b : E → V) : (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := copyGradient a b
  map_add' q r := by
    funext e
    simp only [copyGradient, Pi.add_apply]
    ring
  map_smul' c q := by
    funext e
    simp only [copyGradient, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- A dual boundary annihilates all primal gradients exactly when it annihilates
vertex-indicator gradients. -/
theorem copyBoundary_gradient_eq_zero_iff_indicators {V E W : Type*}
    [Fintype V] [Fintype E] (a b : E → V) (c d : E → W) :
    (∀ (q : V → ℝ) (F : W), copyBoundary c d (copyGradient a b q) F = 0) ↔
    (∀ (v : V) (F : W), copyBoundary c d (copyGradient a b (Pi.single v 1)) F = 0) := by
  classical
  constructor
  · intro h v F
    exact h (Pi.single v 1) F
  · intro h
    let M := (boundaryMap c d).comp (copyGradientMap a b)
    have hM : M = 0 := by
      apply (Pi.basisFun ℝ V).ext
      intro v
      ext F
      simpa only [Pi.basisFun_apply, M, LinearMap.comp_apply, boundaryMap,
        copyGradientMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, Pi.zero_apply]
        using h v F
    intro q F
    have he := LinearMap.congr_fun hM q
    exact congrFun he F

end FiniteAvalanches.Electrical.Plane
