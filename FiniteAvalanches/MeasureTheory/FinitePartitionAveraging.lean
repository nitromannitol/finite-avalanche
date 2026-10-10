import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Fintype.Quotient

/-! Averaging ordinary conditional integrals over a finite equivalence partition. -/
namespace MeasureTheory
open Function
open scoped Classical
noncomputable section

/-- A common bound on every populated equivalence atom bounds the integral
under a finite probability law. The measurable partition is constructed here. -/
theorem integral_le_of_finite_equivalence_cond_bound {X : Type*} [Finite X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
    [IsProbabilityMeasure μ] (s : Setoid X) (f : X → ℝ) (hf : Integrable f μ)
    (B : ℝ) (hpos : ∀ x, μ {y | s.r x y} ≠ 0)
    (hbound : ∀ x, (∫ y, f y ∂ProbabilityTheory.cond μ {y | s.r x y}) ≤ B) :
    (∫ x, f x ∂μ) ≤ B := by
  letI : Fintype (Quotient s) := Fintype.ofFinite _
  let P (q : Quotient s) : Set X := {x | s.r q.out x}
  have hmeas (q : Quotient s) : MeasurableSet (P q) :=
    (Set.toFinite _).measurableSet
  have hcover : (⋃ q, P q) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨Quotient.mk s x, Quotient.mk_out x⟩
  have hdisjoint : Pairwise (Disjoint on P) := by
    intro q q' hne
    apply Set.disjoint_left.mpr
    intro x hx hx'
    have he : Quotient.mk s q.out = Quotient.mk s q'.out :=
      Quotient.sound (s.trans hx (s.symm hx'))
    rw [Quotient.out_eq, Quotient.out_eq] at he
    exact hne he
  have hcell (q : Quotient s) :
      (∫ x in P q, f x ∂μ) ≤ ∫ _ in P q, B ∂μ := by
    have hm0 : μ (P q) ≠ 0 := hpos q.out
    have hmR : (μ (P q)).toReal ≠ 0 :=
      ne_of_gt (ENNReal.toReal_pos hm0 (measure_ne_top _ _))
    have hc := hbound q.out
    change (∫ y, f y ∂ProbabilityTheory.cond μ (P q)) ≤ B at hc
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
      smul_eq_mul] at hc
    have hmul := mul_le_mul_of_nonneg_left hc (ENNReal.toReal_nonneg :
      0 ≤ (μ (P q)).toReal)
    rw [← mul_assoc, mul_inv_cancel₀ hmR, one_mul] at hmul
    simpa only [setIntegral_const, smul_eq_mul, measureReal_def] using hmul
  calc
    (∫ x, f x ∂μ) = ∑ q, ∫ x in P q, f x ∂μ := by
      rw [← integral_iUnion_fintype hmeas hdisjoint (fun _ => hf.integrableOn),
        hcover, Measure.restrict_univ]
    _ ≤ ∑ q, ∫ _ in P q, B ∂μ := Finset.sum_le_sum (fun q _ => hcell q)
    _ = ∫ _ : X, B ∂μ := by
      rw [← integral_iUnion_fintype hmeas hdisjoint
        (fun _ => (integrable_const B).integrableOn), hcover, Measure.restrict_univ]
    _ = B := by rw [integral_const, probReal_univ, one_smul]

end
end MeasureTheory
