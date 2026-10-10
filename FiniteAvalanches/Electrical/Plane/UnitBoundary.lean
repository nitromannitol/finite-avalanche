import FiniteAvalanches.Electrical.Plane.DirectedPaths
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Literal finite copied unit-flow divergence and its potential pairing. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

noncomputable def unitBoundary {V E : Type*} (a b : E → V) (S : Finset E) (x : V) : ℝ :=
  ∑ e ∈ S, ((if a e = x then 1 else 0)-(if b e = x then 1 else 0))

/-- A finite-copy divergence is the outgoing unit count minus the incoming unit count. -/
theorem unitBoundary_eq_sub {V E : Type*} (a b : E → V) (S : Finset E) (x : V) :
    unitBoundary a b S x = (∑ e ∈ S, if a e = x then (1 : ℝ) else 0)-
      ∑ e ∈ S, if b e = x then (1 : ℝ) else 0 := by
  simp only [unitBoundary,Finset.sum_sub_distrib]

/-- The literal incidence-potential pairing retains every named copy. -/
theorem sum_mul_unitBoundary {V E : Type*} [Fintype V]
    (a b : E → V) (S : Finset E) (H : V → ℝ) :
    (∑ x, H x*unitBoundary a b S x) = ∑ e ∈ S, (H (a e)-H (b e)) := by
  simp only [unitBoundary,Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mul_sub,mul_ite,mul_one,mul_zero,Finset.sum_sub_distrib,
    Finset.sum_ite_eq,Finset.mem_univ,if_true]

/-- A balanced finite flow supported on strictly increasing copies has no edges. -/
theorem eq_empty_of_unitBoundary_zero {V E : Type*} [Fintype V]
    (a b : E → V) (S : Finset E) (H : V → ℝ)
    (hi : ∀ e ∈ S, H (a e) < H (b e))
    (hb : ∀ x, unitBoundary a b S x = 0) : S = ∅ := by
  by_contra hne
  have hs : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  have hsum := sum_mul_unitBoundary a b S H
  simp only [hb,mul_zero,Finset.sum_const_zero] at hsum
  have hn : (∑ e ∈ S, (H (a e)-H (b e))) < 0 :=
    Finset.sum_neg (fun e he => sub_neg.mpr (hi e he)) hs
  exact (ne_of_lt hn) hsum.symm

/-- A unit source or an actual incoming copy forces an outgoing copy before the sink. -/
theorem exists_outgoing_of_unitBoundary {V E : Type*}
    (a b : E → V) (S : Finset E) (s t x : V)
    (hB : ∀ y, unitBoundary a b S y = (if s = y then 1 else 0)-(if t = y then 1 else 0))
    (hxt : x ≠ t) (hx : x = s ∨ ∃ e ∈ S, b e = x) :
    ∃ e ∈ S, a e = x := by
  by_contra hnone
  have hnone' : ∀ e ∈ S, a e ≠ x := by
    intro e he hax
    exact hnone ⟨e,he,hax⟩
  have hout : (∑ e ∈ S, if a e = x then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero (fun e he => if_neg (hnone' e he))
  have hin : 0 ≤ ∑ e ∈ S, if b e = x then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun e _ => by split_ifs <;> norm_num)
  have hbalance := hB x
  rw [unitBoundary_eq_sub,hout,if_neg hxt.symm,sub_zero] at hbalance
  by_cases hxs : s = x
  · rw [if_pos hxs] at hbalance
    linarith only [hbalance,hin]
  · rw [if_neg hxs] at hbalance
    rcases hx with hx | ⟨e,he,hbx⟩
    · exact hxs hx.symm
    · have hpos : 0 < ∑ e ∈ S, if b e = x then (1 : ℝ) else 0 := by
        apply Finset.sum_pos'
        · intro e _; split_ifs <;> norm_num
        · exact ⟨e,he,by rw [if_pos hbx]; norm_num⟩
      linarith only [hbalance,hpos]

end FiniteAvalanches.Electrical.Plane
