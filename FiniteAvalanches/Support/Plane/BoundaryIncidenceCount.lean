import FiniteAvalanches.Support.Plane.BoundaryGradientBasis
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Signed face-boundary incidence counts

The dual boundary of the gradient of a vertex indicator is the signed
balance of the four possible primal and dual endpoint incidences.
-/

namespace FiniteAvalanches.Electrical.Plane

open scoped Classical BigOperators

/-- An indicator-gradient boundary is the difference of two sums of incidence counts. -/
theorem copyBoundary_indicator_gradient_eq_counts {V E W : Type*} [Fintype E]
    (a b : E → V) (c d : E → W) (v : V) (F : W) :
    copyBoundary c d (copyGradient a b (Pi.single v 1)) F =
      ((Finset.univ.filter fun e => c e = F ∧ a e = v).card : ℝ) +
      ((Finset.univ.filter fun e => d e = F ∧ b e = v).card : ℝ) -
      ((Finset.univ.filter fun e => c e = F ∧ b e = v).card : ℝ) -
      ((Finset.univ.filter fun e => d e = F ∧ a e = v).card : ℝ) := by
  classical
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.natCast_card_filter, Finset.natCast_card_filter]
  unfold copyBoundary
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [copyGradient, Pi.single_apply]
  split_ifs <;> simp_all

end FiniteAvalanches.Electrical.Plane
