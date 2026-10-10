module

public import FiniteAvalanches.Electrical.Geometry.Angular
public import FiniteAvalanches.Electrical.Geometry.DyadicSum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Logarithmic energy for actual disjoint square interiors. -/

@[expose] public section

namespace FiniteAvalanches.Electrical.Geometry

open Set
open scoped BigOperators Classical

/-- Real oscillation on a nonempty domain with bounded pairwise differences. -/
noncomputable def oscillation (F : ℝ × ℝ → ℝ) (S : Set (ℝ × ℝ))
    (_hS : S.Nonempty) (_hB : ∃ B, ∀ z ∈ S, ∀ w ∈ S, |F z - F w| ≤ B) : ℝ :=
  sSup {v | ∃ z ∈ S, ∃ w ∈ S, v = |F z - F w|}

theorem Square.carrier_nonempty (Q : Square) : Q.carrier.Nonempty :=
  ⟨(Q.x,Q.y), ⟨⟨le_rfl, by linarith [Q.side_nonneg]⟩,
    ⟨le_rfl, by linarith [Q.side_nonneg]⟩⟩⟩

theorem oscillation_le {F : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} {B : ℝ}
    (hS : S.Nonempty) (hB : ∃ B, ∀ z ∈ S, ∀ w ∈ S, |F z-F w| ≤ B)
    (h : ∀ z ∈ S, ∀ w ∈ S, |F z-F w| ≤ B) :
    oscillation F S hS hB ≤ B := by
  obtain ⟨z,hz⟩ := hS
  apply csSup_le
  · exact ⟨0,z,hz,z,hz,by simp⟩
  · rintro v ⟨z,hz,w,hw,rfl⟩
    exact h z hz w hw

theorem abs_sub_le_oscillation {F : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    {z w : ℝ × ℝ} (hz : z ∈ S) (hw : w ∈ S)
    (h : ∃ B, ∀ z ∈ S, ∀ w ∈ S, |F z-F w| ≤ B) :
    |F z-F w| ≤ oscillation F S ⟨z, hz⟩ h := by
  apply le_csSup
  · obtain ⟨B,hB⟩ := h
    exact ⟨B,by rintro v ⟨z,hz,w,hw,rfl⟩; exact hB z hz w hw⟩
  · exact ⟨z,hz,w,hw,rfl⟩

/-- Oscillation is the least upper bound of the actual pairwise differences. -/
theorem oscillation_le_iff {F : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hS : S.Nonempty) (hB : ∃ B, ∀ z ∈ S, ∀ w ∈ S, |F z-F w| ≤ B) (B : ℝ) :
    oscillation F S hS hB ≤ B ↔ ∀ z ∈ S, ∀ w ∈ S, |F z-F w| ≤ B := by
  constructor
  · intro h z hz w hw
    exact (abs_sub_le_oscillation hz hw hB).trans h
  · exact oscillation_le hS hB

/-- The angular oscillation on a closed dilated square, for positive epsilon. -/
noncomputable def Square.angularOsc (Q : Square) (epsilon y0 lambda : ℝ)
    (hl : 1 ≤ lambda) (he : 0 < epsilon) : ℝ :=
  oscillation (angular epsilon y0) (Q.dilate lambda (by linarith)).carrier
    (Q.dilate lambda (by linarith)).carrier_nonempty
    ⟨1, fun z _ w _ => angular_sub_le_one epsilon y0 he z w⟩

theorem Square.angularOsc_bounds (Q : Square) (epsilon y0 lambda : ℝ)
    (he : 0 < epsilon) (hl : 1 ≤ lambda) :
    0 ≤ Q.angularOsc epsilon y0 lambda hl he ∧
      Q.angularOsc epsilon y0 lambda hl he ≤ 1 ∧
      Q.angularOsc epsilon y0 lambda hl he ≤ 4*lambda^2*Q.side/Q.scale epsilon y0 := by
  have hS := (Q.dilate lambda (by linarith)).carrier_nonempty
  obtain ⟨z,hz⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · have h := abs_sub_le_oscillation (F := angular epsilon y0) hz hz
      ⟨1,fun z _ w _ => angular_sub_le_one epsilon y0 he z w⟩
    simpa [Square.angularOsc] using h
  · exact oscillation_le ⟨z,hz⟩ _ (fun z _ w _ => angular_sub_le_one epsilon y0 he z w)
  · exact oscillation_le ⟨z,hz⟩ _ (fun z hz w hw => angular_sub_le_scale Q epsilon y0 lambda he hl z w hz hw)

/-- A dyadic class is charged to actual area, with both the thick and thin bounds. -/
theorem angular_bin_energy_le {I : Type*} (s : Finset I) (Q : I → Square)
    (hd : Set.PairwiseDisjoint (↑s) (fun i => (Q i).openCarrier))
    (M epsilon y0 lambda rho : ℝ) (hM : 0 ≤ M) (he : 0 < epsilon)
    (hl : 1 ≤ lambda) (hr : 0 < rho)
    (hQ : ∀ i ∈ s, (Q i).carrier ⊆ rectangle 0 1 0 M)
    (hscale : ∀ i ∈ s, rho ≤ (Q i).scale epsilon y0 ∧ (Q i).scale epsilon y0 ≤ 2*rho) :
    (∑ i ∈ s, ((Q i).angularOsc epsilon y0 lambda hl he)^2) ≤
      64*(4*lambda^2)^2 * min 1 (min 1 M/rho) := by
  let A := ∑ i ∈ s, (Q i).side^2
  let C := 4*lambda^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp := sum_sq_side_le_local_area s Q hd M y0 rho hM hr.le hQ
    (fun i hi => (Q i).carrier_subset_box_of_scale_le epsilon y0 rho (hscale i hi).2)
  have harea : A ≤ 64*rho^2 ∧ A ≤ 8*min 1 M*rho :=
    ⟨hp.trans (min_le_left _ _), hp.trans (min_le_right _ _)⟩
  have hsum : (∑ i ∈ s, ((Q i).angularOsc epsilon y0 lambda hl he)^2) ≤ C^2/rho^2*A := by
    calc
      _ ≤ ∑ i ∈ s, C^2/rho^2*(Q i).side^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hb := (Q i).angularOsc_bounds epsilon y0 lambda he hl
        have hbound : (Q i).angularOsc epsilon y0 lambda hl he ≤ C*(Q i).side/rho :=
          hb.2.2.trans (div_le_div_of_nonneg_left (mul_nonneg hC (Q i).side_nonneg)
            hr (hscale i hi).1)
        have hh := mul_self_le_mul_self hb.1 hbound
        calc
          _ ≤ (C*(Q i).side/rho)^2 := by simpa only [pow_two] using hh
          _ = C^2/rho^2*(Q i).side^2 := by ring
      _ = C^2/rho^2*A := by rw [Finset.mul_sum]
  have hcoef : 0 ≤ C^2/rho^2 := by positivity
  have hb : (∑ i ∈ s, ((Q i).angularOsc epsilon y0 lambda hl he)^2) ≤ 64*C^2 := by
    calc
      _ ≤ C^2/rho^2*(64*rho^2) := hsum.trans (mul_le_mul_of_nonneg_left harea.1 hcoef)
      _ = 64*C^2 := by field_simp
  have ht : (∑ i ∈ s, ((Q i).angularOsc epsilon y0 lambda hl he)^2) ≤ 64*C^2*(min 1 M/rho) := by
    have htheta : 0 ≤ min 1 M := le_min (by norm_num) hM
    calc
      _ ≤ C^2/rho^2*(8*min 1 M*rho) := hsum.trans (mul_le_mul_of_nonneg_left harea.2 hcoef)
      _ = 8*C^2*(min 1 M/rho) := by field_simp
      _ ≤ 64*C^2*(min 1 M/rho) := by nlinarith [sq_nonneg C, div_nonneg htheta hr.le]
  change _ ≤ 64*C^2*min 1 (min 1 M/rho)
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ 64*C^2), mul_one]
  exact le_min hb ht

/-- Complete geometric logarithmic bound: packing is proved from disjointness, not assumed. -/
theorem angular_energy_le_log {I : Type*} (s : Finset I) (Q : I → Square)
    (hd : Set.PairwiseDisjoint (↑s) (fun i => (Q i).openCarrier))
    (M epsilon y0 lambda : ℝ) (hM : 0 ≤ M) (he : 0 < epsilon)
    (heM : epsilon ≤ min 1 M) (hl : 1 ≤ lambda)
    (hQ : ∀ i ∈ s, (Q i).carrier ⊆ rectangle 0 1 0 M) :
    (∑ i ∈ s, ((Q i).angularOsc epsilon y0 lambda hl he)^2) ≤
      64*(4*lambda^2)^2 * (3 + Real.log (min 1 M/epsilon)/Real.log 2) := by
  choose k hk using fun i : I => exists_dyadic_bin epsilon ((Q i).scale epsilon y0)
    he ((Q i).scale_bounds epsilon y0).1
  let N := s.sup k + 1
  have hkN : ∀ i ∈ s, k i ∈ Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hi))
  have hpart : (∑ i ∈ s, ((Q i).angularOsc epsilon y0 lambda hl he)^2) =
      ∑ j ∈ Finset.range N, ∑ i ∈ s with k i = j, ((Q i).angularOsc epsilon y0 lambda hl he)^2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [hkN i hi]
  rw [hpart]
  calc
    _ ≤ ∑ j ∈ Finset.range N, 64*(4*lambda^2)^2*min 1 (min 1 M/(2^j*epsilon)) := by
      apply Finset.sum_le_sum
      intro j _
      apply angular_bin_energy_le (s.filter (fun i => k i = j)) Q
        (hd.subset (by intro i hi; exact (Finset.mem_filter.mp hi).1)) M epsilon y0 lambda
        (2^j*epsilon) hM he hl (by positivity)
      · intro i hi
        exact hQ i (Finset.mem_filter.mp hi).1
      · intro i hi
        have heq := (Finset.mem_filter.mp hi).2
        have h := hk i
        rw [heq] at h
        constructor
        · exact h.1
        · have hpow : (2:ℝ)^(j+1)*epsilon = 2*(2^j*epsilon) := by rw [pow_succ]; ring
          rw [hpow] at h
          exact h.2.le
    _ = 64*(4*lambda^2)^2 * (∑ j ∈ Finset.range N, min 1 ((min 1 M/epsilon)/2^j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dyadic_sum_le_log (min 1 M/epsilon) ((le_div_iff₀ he).mpr (by simpa using heM)) N)
      (by positivity)

end FiniteAvalanches.Electrical.Geometry
