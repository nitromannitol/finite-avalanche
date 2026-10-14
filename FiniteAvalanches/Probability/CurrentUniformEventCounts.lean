import FiniteAvalanches.Trees.Measure
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.CurrentUniformEventCounts
open MeasureTheory
open scoped Classical BigOperators
noncomputable section

/-- A finite uniform event is the true count of its successful original outcomes. -/
theorem uniform_event_real_eq (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (A : Set Ω) :
    (uniformMeasure Ω).real A = (∑ t : Ω, if t ∈ A then (1 : ℝ) else 0) / Nat.card Ω := by
  rw [uniformMeasure_real_apply, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_boole]

/-- Interchanging the two genuine finite counts aggregates event probabilities. -/
theorem uniform_event_sum_eq (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {I : Type*} (s : Finset I) (A : I → Set Ω) :
    ∑ e ∈ s, (uniformMeasure Ω).real (A e) =
      (∑ t : Ω, ((s.filter (fun e => t ∈ A e)).card : ℝ)) / Nat.card Ω := by
  simp_rw [uniform_event_real_eq]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact Finset.sum_boole _ _

/-- Pointwise actual outcome-count domination gives the same normalized real sum. -/
theorem uniform_event_sum_le (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {I J : Type*} (s : Finset I) (v : Finset J) (A : I → Set Ω) (B : J → Set Ω)
    (h : ∀ t : Ω, (s.filter (fun e => t ∈ A e)).card ≤ (v.filter (fun x => t ∈ B x)).card) :
    ∑ e ∈ s, (uniformMeasure Ω).real (A e) ≤ ∑ x ∈ v, (uniformMeasure Ω).real (B x) := by
  rw [uniform_event_sum_eq, uniform_event_sum_eq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun t _ => Nat.cast_le.mpr (h t))

end
end FiniteAvalanches.CurrentUniformEventCounts

#print FiniteAvalanches.CurrentUniformEventCounts.uniform_event_real_eq
#print axioms FiniteAvalanches.CurrentUniformEventCounts.uniform_event_real_eq
#print FiniteAvalanches.CurrentUniformEventCounts.uniform_event_sum_eq
#print axioms FiniteAvalanches.CurrentUniformEventCounts.uniform_event_sum_eq
#print FiniteAvalanches.CurrentUniformEventCounts.uniform_event_sum_le
#print axioms FiniteAvalanches.CurrentUniformEventCounts.uniform_event_sum_le
