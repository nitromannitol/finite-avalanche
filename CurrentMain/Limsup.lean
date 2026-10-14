import FiniteAvalanches.Trees.Lattice.CurrentSourceReciprocal
import Mathlib.Order.LiminfLimsup

/-! Uniform bounds for the source reciprocal pass to the finite-box limsup. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Paper.CurrentMain
open LatticeProb FiniteAvalanches.Sandpile SourceCounting TreeMeasurability11
open TreeMeasurability11.CurrentDomain MeasureTheory Filter
open scoped Classical
noncomputable section

/-- Only valid volumes enter the eventual expectation comparison. -/
theorem source_reciprocal_mean_eq_auxiliary {r N : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    (∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
      (fun _ hx => sourceMarks_inBox hr hrN hx) t ∂WiredTrees.law N) =
      ∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂WiredTrees.law N := by
  apply integral_congr_ae
  exact Eventually.of_forall fun t => sourceFiniteReciprocal_eq_auxiliary N
    (sourceMarks r) (Finset.insert_nonempty _ _)
    (fun _ hx => sourceMarks_inBox hr hrN hx) t

/-- A valid-volume bound controls the real limsup without an expectation limit. -/
theorem finite_reciprocal_limsup_le_source_bound {r : ℕ} (hr : 2 ≤ r) (B : ℝ)
    (hB : ∀ N : ℕ, ∀ hrN : r ≤ N,
      (∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t ∂WiredTrees.law N) ≤ B) :
    limsup (fun N : ℕ => ∫ t, finiteZN N (sourceMarks r)
      (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) atTop ≤ B := by
  have hnonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ ∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t
        ∂WiredTrees.law N := by
    filter_upwards [eventually_ge_atTop r] with N hrN
    rw [← source_reciprocal_mean_eq_auxiliary hr hrN]
    apply integral_nonneg
    intro t
    exact (sourceFiniteReciprocal_bounds N (sourceMarks r) (Finset.insert_nonempty _ _)
      (fun _ hx => sourceMarks_inBox hr hrN hx) t).1
  apply limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop hnonneg)
  filter_upwards [eventually_ge_atTop r] with N hrN
  rw [← source_reciprocal_mean_eq_auxiliary hr hrN]
  exact hB N hrN

end
end FiniteAvalanches.Paper.CurrentMain
