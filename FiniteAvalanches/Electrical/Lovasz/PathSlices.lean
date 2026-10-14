import FiniteAvalanches.Electrical.Plane.SquareSlices
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Closed coverage and disjoint open intervals along a finite increasing cut
path. Generic voltage levels can be chosen in every nonempty open interval. -/

namespace FiniteAvalanches.Electrical.Lovasz
open scoped Classical

/-- Every interval contains a voltage level different from all finite vertex values. -/
theorem exists_generic_voltage {V : Type} [Fintype V] (phi : V → ℝ)
    (a b : ℝ) (hab : a < b) :
    ∃ t : ℝ, a < t ∧ t < b ∧ ∀ x : V, phi x ≠ t := by
  obtain ⟨t, ht, hnot⟩ := (Set.Ioo_infinite hab).exists_notMem_finite (Set.finite_range phi)
  exact ⟨t, ht.1, ht.2, fun x h => hnot ⟨x, h⟩⟩

/-- The closed consecutive intervals of a nonempty increasing finite path cover
the whole closed interval between its endpoints. -/
theorem fin_path_interval_cover (m : ℕ) (hm : 0 < m) (H : Fin (m + 1) → ℝ)
    (hstep : ∀ i : Fin m, H i.castSucc < H i.succ)
    (u : ℝ) (hu0 : H 0 ≤ u) (hu1 : u ≤ H (Fin.last m)) :
    ∃ i : Fin m, H i.castSucc ≤ u ∧ u ≤ H i.succ := by
  have cover (k : Fin (m + 1)) : H 0 ≤ u → u ≤ H k →
      ∃ i : Fin m, H i.castSucc ≤ u ∧ u ≤ H i.succ := by
    induction k using Fin.induction with
    | zero =>
      intro hlo hhi
      refine ⟨⟨0, hm⟩, hlo, ?_⟩
      exact hhi.trans (hstep ⟨0, hm⟩).le
    | succ i ih =>
      intro hlo hhi
      by_cases hmid : u ≤ H i.castSucc
      · exact ih hlo hmid
      · exact ⟨i, (lt_of_not_ge hmid).le, hhi⟩
  exact cover (Fin.last m) hu0 hu1

/-- Distinct entries of an increasing finite path have disjoint open intervals. -/
theorem fin_path_interval_disjoint (m : ℕ) (H : Fin (m + 1) → ℝ)
    (hstep : ∀ i : Fin m, H i.castSucc < H i.succ)
    (i j : Fin m) (hij : i ≠ j) :
    Disjoint (Set.Ioo (H i.castSucc) (H i.succ)) (Set.Ioo (H j.castSucc) (H j.succ)) := by
  have hmono : StrictMono H := Fin.strictMono_iff_lt_succ.mpr hstep
  have forward (k l : Fin m) (hkl : k < l) :
      Disjoint (Set.Ioo (H k.castSucc) (H k.succ)) (Set.Ioo (H l.castSucc) (H l.succ)) := by
    have hidx : k.succ ≤ l.castSucc := by
      change k.val + 1 ≤ l.val
      exact Nat.succ_le_of_lt hkl
    apply Set.disjoint_left.mpr
    intro u hku hlu
    exact (not_lt_of_ge ((hmono.monotone hidx).trans hlu.1.le)) hku.2
  rcases lt_or_gt_of_ne hij with h | h
  · exact forward i j h
  · exact (forward j i h).symm

/-- The generic voltage levels are dense up to both closed normalized endpoints. -/
theorem closure_generic_voltage_levels {V : Type} [Fintype V] (phi : V → ℝ) :
    closure {t : ℝ | 0 < t ∧ t < 1 ∧ ∀ x : V, phi x ≠ t} = Set.Icc 0 1 := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_Icc
    intro t ht
    exact ⟨ht.1.le, ht.2.1.le⟩
  · have hd : Set.Ioo (0 : ℝ) 1 ⊆ closure {t : ℝ | 0 < t ∧ t < 1 ∧ ∀ x : V, phi x ≠ t} := by
      intro t ht
      rw [Metric.mem_closure_iff]
      intro epsilon he
      have hlo : max 0 (t - epsilon) < t := max_lt ht.1 (by linarith only [he])
      have hhi : t < min 1 (t + epsilon) := lt_min ht.2 (by linarith only [he])
      obtain ⟨s, hs0, hs1, hsg⟩ := exists_generic_voltage phi
        (max 0 (t - epsilon)) (min 1 (t + epsilon)) (hlo.trans hhi)
      refine ⟨s, ⟨(le_max_left _ _).trans_lt hs0, hs1.trans_le (min_le_left _ _), hsg⟩, ?_⟩
      rw [Real.dist_eq]
      apply abs_lt.mpr
      constructor
      · linarith only [hs1, min_le_right (1 : ℝ) (t + epsilon)]
      · linarith only [hs0, le_max_right (0 : ℝ) (t - epsilon)]
    have h := closure_mono hd
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_closure] at h
    exact h

end FiniteAvalanches.Electrical.Lovasz

#print axioms FiniteAvalanches.Electrical.Lovasz.exists_generic_voltage
#print axioms FiniteAvalanches.Electrical.Lovasz.fin_path_interval_cover
#print axioms FiniteAvalanches.Electrical.Lovasz.fin_path_interval_disjoint
#print axioms FiniteAvalanches.Electrical.Lovasz.closure_generic_voltage_levels
