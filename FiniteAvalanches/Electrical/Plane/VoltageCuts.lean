import FiniteAvalanches.Electrical.Plane.Ranges

/-! Literal copied voltage cuts and their exact total current, before any dual-path theorem. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- Original edge-copy IDs crossing the strict lower voltage level. -/
noncomputable def crossingEdges {V E : Type*} [Fintype E]
    (a b : E → V) (phi : V → ℝ) (t : ℝ) : Finset E :=
  Finset.univ.filter (fun e =>
    (phi (a e) < t ∧ t ≤ phi (b e)) ∨ (phi (b e) < t ∧ t ≤ phi (a e)))

@[simp] theorem mem_crossingEdges {V E : Type*} [Fintype E]
    (a b : E → V) (phi : V → ℝ) (t : ℝ) (e : E) :
    e ∈ crossingEdges a b phi t ↔
      (phi (a e) < t ∧ t ≤ phi (b e)) ∨ (phi (b e) < t ∧ t ≤ phi (a e)) := by
  simp [crossingEdges]

private theorem cutoff_current (u v t : ℝ) :
    (u-v)*((if u < t then (1 : ℝ) else 0)-(if v < t then 1 else 0)) =
      -(if (u < t ∧ t ≤ v) ∨ (v < t ∧ t ≤ u) then |u-v| else 0) := by
  by_cases hu : u < t
  · by_cases hv : v < t
    · simp [hu,hv,not_le.mpr hu,not_le.mpr hv]
    · have htv := le_of_not_gt hv
      have huv : u-v < 0 := sub_neg.mpr (hu.trans_le htv)
      simp [hu,hv,htv,abs_of_neg huv]
  · by_cases hv : v < t
    · have htu := le_of_not_gt hu
      have huv : 0 < u-v := sub_pos.mpr (hv.trans_le htu)
      simp [hu,hv,htu,abs_of_pos huv]
    · simp [hu,hv]

/-- Kirchhoff and normalized terminal flux give the actual crossing-copy current sum. -/
theorem sum_crossing_current_eq_energy {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (alpha beta : V) (hne : alpha ≠ beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (∑ e ∈ crossingEdges a b phi t, |phi (a e)-phi (b e)|) = energy a b phi := by
  let w : V → ℝ := fun x => if phi x < t then 1 else 0
  have hx (x : V) : w x*laplacian a b phi x =
      if x = alpha then -energy a b phi else 0 := by
    by_cases hxa : x = alpha
    · subst x
      rw [if_pos rfl,(terminal_flux_eq_energy a b phi alpha beta hne hp0 hp1 hh).1]
      simp only [w,hp0,if_pos ht0,one_mul]
    · by_cases hxb : x = beta
      · subst x
        have hbt : ¬ phi beta < t := by rw [hp1]; exact not_lt.mpr ht1.le
        simp only [w,if_neg hbt,zero_mul,if_neg hxa]
      · rw [hh x hxa hxb,mul_zero,if_neg hxa]
  have hi := incidence_sum a b phi w
  rw [Finset.sum_congr rfl (fun x _ => hx x)] at hi
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at hi
  have he (e : E) : (phi (a e)-phi (b e))*(w (a e)-w (b e)) =
      -(if e ∈ crossingEdges a b phi t then |phi (a e)-phi (b e)| else 0) := by
    simp only [mem_crossingEdges]
    exact cutoff_current (phi (a e)) (phi (b e)) t
  rw [Finset.sum_congr rfl (fun e _ => he e),Finset.sum_neg_distrib] at hi
  have heq := neg_injective hi.symm
  simpa only [crossingEdges,Finset.sum_filter,Finset.mem_filter,Finset.mem_univ,true_and] using heq

/-- At a generic source slice both strict voltage sides are connected, and its copied currents sum to M. -/
theorem voltage_slice_current {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (alpha beta : V) (hne : alpha ≠ beta)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ((supportGraph a b).induce {x | phi x < t}).Connected ∧
    ((supportGraph a b).induce {x | t < phi x}).Connected ∧
    (∑ e ∈ crossingEdges a b phi t, |phi (a e)-phi (b e)|) = energy a b phi := by
  obtain ⟨hl,hu⟩ := (voltage_range_and_levels a b alpha beta hc phi hp0 hp1 hh).2 t ht0 ht1
  exact ⟨hl,hu,sum_crossing_current_eq_energy a b alpha beta hne phi hp0 hp1 hh t ht0 ht1⟩

end FiniteAvalanches.Electrical.Plane
