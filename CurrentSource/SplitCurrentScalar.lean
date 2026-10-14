import FiniteAvalanches.Electrical.Physical.Undilated.Meaning
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The current split proof's final sixteen/twenty-one scalar assembly. -/

namespace FiniteAvalanches.Electrical.Source.CurrentSplit
open FiniteAvalanches.Electrical.Geometry
open FiniteAvalanches.Electrical.Physical.Undilated
open scoped BigOperators Classical

/-- The source normalization p/2 yields exactly log(2/p). -/
theorem log_inv_half_current (p : ℝ) : Real.log (1 / (p / 2)) = Real.log (2 / p) := by
  congr 1
  ring

/-- The logarithmic factor is at least one for every source boundary current. -/
theorem one_le_log_factor (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    1 ≤ 1 + Real.log (2 / p) := by
  have htwo : 1 ≤ 2 / p := (le_div_iff₀ hp).mpr
    (by simpa only [one_mul] using hp1.trans (show (1 : ℝ) ≤ 2 by norm_num))
  exact le_add_of_nonneg_right (Real.log_nonneg htwo)

/-- All current-proof constants combine before any scale, drawing or current is chosen. -/
theorem current_split_scalar_bound (p g S W : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hg : g ≤ W) (htransfer : W ≤ 1 + 21 * S)
    (hsquares : S ≤ 16 * (1 + Real.log (2 / p))) :
    g ≤ 1 + 336 * (1 + Real.log (2 / p)) ∧
      g ≤ 337 * (1 + Real.log (2 / p)) ∧
      g ≤ 1 + 3888 * (1 + Real.log (2 / p)) := by
  have hlog := one_le_log_factor p hp hp1
  have hnew : g ≤ 1 + 336 * (1 + Real.log (2 / p)) := by
    linarith only [hg, htransfer, hsquares]
  exact ⟨hnew, by linarith only [hnew, hlog], by linarith only [hnew, hlog]⟩

/-- The one universal constant belongs outside every allowed boundary current. -/
theorem exists_uniform_current_split_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ p g S W : ℝ, 0 < p → p ≤ 1 → g ≤ W →
      W ≤ 1 + 21 * S → S ≤ 16 * (1 + Real.log (2 / p)) →
      g ≤ C * (1 + Real.log (2 / p)) := by
  refine ⟨337, by norm_num, ?_⟩
  intro p g S W hp hp1 hg ht hs
  exact (current_split_scalar_bound p g S W hp hp1 hg ht hs).2.1

/-- Exact physical-square16 application at the current boundary-current normalization. -/
theorem original_square_sum_at_current {I : Type*} (s : Finset I) (Q : I → Square)
    (hd : Set.PairwiseDisjoint (↑s) (fun i => (Q i).openCarrier))
    (p y0 : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hQ : ∀ i ∈ s, (Q i).carrier ⊆ Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) :
    (∑ i ∈ s, ((Q i).angularOsc (p / 2) y0 1 (by norm_num) (by positivity)) ^ 2) ≤
      16 * (1 + Real.log (2 / p)) := by
  have h := angular_square_sum_le_sixteen s Q hd (p / 2) y0
    (by positivity) (by linarith only [hp1]) hQ
  rw [log_inv_half_current] at h
  exact h

end FiniteAvalanches.Electrical.Source.CurrentSplit
