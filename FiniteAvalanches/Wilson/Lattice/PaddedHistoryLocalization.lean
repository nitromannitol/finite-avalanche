import FiniteAvalanches.Wilson.Lattice.NestedBoxStepThree

/-! Three extra box layers allow a closed low-contact event without a boundary assumption. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.PaddedHistoryLocalization
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open ActualQueryPrefixes ActualLocalizationUnion ReciprocalStepThree
open scoped Classical
noncomputable section

theorem padded_sixth_power_margin (r : ℕ) (hr : 2 ≤ r) :
    4 * (3 * r + 4) + 4 ≤ r ^ 6 - 1 := by
  have hsq : 4 ≤ r ^ 2 := by nlinarith only [hr]
  have h3 : 4 * r ≤ r ^ 3 := by
    simpa only [pow_succ] using Nat.mul_le_mul_right r hsq
  have h8 : 8 ≤ r ^ 3 := by
    have h := Nat.pow_le_pow_left hr 3
    norm_num at h
    exact h
  have h6 : 32 * r ≤ r ^ 6 := by
    calc
      _ = 8 * (4 * r) := by omega
      _ ≤ 8 * r ^ 3 := Nat.mul_le_mul_left 8 h3
      _ ≤ r ^ 3 * r ^ 3 := Nat.mul_le_mul_right (r ^ 3) h8
      _ = r ^ 6 := by rw [← pow_add]
  omega

theorem padded_query_scalar (D r : ℝ) (hD : 0 ≤ D) (hr : 2 ≤ r) :
    (6 * r + 9) ^ 2 * D * Real.sqrt ((3 * r + 5) / r ^ 6) ≤
      (1024 * D) * r ^ (-(1 / 2 : ℝ)) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hc : (6 * r + 9) ^ 2 ≤ 4 * (6 * r + 3) ^ 2 := by nlinarith only [hr]
  have hw : Real.sqrt ((3 * r + 5) / r ^ 6) ≤
      2 * Real.sqrt ((3 * r + 2) / r ^ 6) := by
    calc
      _ ≤ Real.sqrt (4 * ((3 * r + 2) / r ^ 6)) := Real.sqrt_le_sqrt (by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith only [hr]) (pow_nonneg hr0.le _))
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  calc
    _ ≤ (4 * (6 * r + 3) ^ 2) * D * (2 * Real.sqrt ((3 * r + 2) / r ^ 6)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc hD) hw (Real.sqrt_nonneg _) (by positivity)
    _ = 8 * ((6 * r + 3) ^ 2 * D * Real.sqrt ((3 * r + 2) / r ^ 6)) := by ring
    _ ≤ 8 * ((128 * D) * r ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (query_sixth_power_bound_mul D r hD hr) (by norm_num)
    _ = _ := by ring

/-- The same actual distinct first rows control an arbitrary concatenated list
in the padded box; all terminal vertices remain in the exit event. -/
theorem padded_box_list_history_escape : ∃ D : ℝ, 0 < D ∧
    ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected → (0 : Site 2) ∈ K →
    ∀ R : RootPair, (K : Set (Site 2)) ⊆ R.zero →
    ∀ r : ℕ, 2 ≤ r →
      16 * r ^ 6 ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
    ∀ L : List (Site 2), (∀ x ∈ L, x ∈ boxSites (3 * r + 4)) →
      wilsonRows (prefixExit R L (r ^ 6)) ≤
        ENNReal.ofReal (D * (r : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨D, hD, hbound⟩ := DistinctStartLocalization.finite_stopped_history_distinct_bound
  refine ⟨1024 * D, mul_pos (by norm_num) hD, ?_⟩
  intro K hK h0 R hKR r hr hdiam L hL
  have hmargin := padded_sixth_power_margin r hr
  have hboundary : ∃ z ∈ K, siteRadius 0 z = r ^ 6 - 1 :=
    connected_boundary_of_diameter K hK.preconnected h0 (r ^ 6 - 1) (by omega) (by omega)
  have hqueries : ∀ x ∈ L, siteRadius 0 x ≤ 3 * r + 4 :=
    fun x hx => (site_radius_zero_le_iff x _).mpr (hL x hx)
  have hb := hbound (K : Set (Site 2)) hK.preconnected h0 R hKR
    (3 * r + 4) (r ^ 6) (padded_sixth_power_margin r hr) hboundary L hqueries
  have hc : L.toFinset.card ≤ (6 * r + 9) ^ 2 := by
    calc
      _ ≤ (boxSites (3 * r + 4)).card := Finset.card_le_card (by
        intro x hx
        exact hL x (List.mem_toFinset.mp hx))
      _ = (6 * r + 9) ^ 2 := by rw [card_box_sites]; congr 1; omega
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hc' : (L.toFinset.card : ℝ) ≤ (6 * (r : ℝ) + 9) ^ 2 := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc' hD.le) (Real.sqrt_nonneg (((3 * r + 4 + 1 : ℕ) : ℝ) / r ^ 6))
  have hs := padded_query_scalar D (r : ℝ) hD.le (by exact_mod_cast hr)
  push_cast at hm
  rw [show (3 : ℝ) * r + 4 + 1 = 3 * r + 5 by ring] at hm
  push_cast
  rw [show (3 : ℝ) * r + 4 + 1 = 3 * r + 5 by ring]
  exact hm.trans hs

/-- Each actual start belongs to the last scale's padded box, without any
permutation or equality claim about the complete stopped history. -/
theorem queryPrefix_padded_starts (s a : ℕ → ℕ) (hs : Monotone s)
    (ha : ∀ j, a j ≤ s j + 1) (i : ℕ) :
    ∀ x ∈ queryPrefix (fun j => (boxSites (3 * a j + 1)).toList) (i + 1),
      x ∈ boxSites (3 * s i + 4) := by
  induction i with
  | zero =>
    intro x hx
    simp only [queryPrefix, List.nil_append] at hx
    exact box_sites_mono (by have h := ha 0; omega) (Finset.mem_toList.mp hx)
  | succ i ih =>
    intro x hx
    rw [queryPrefix] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact box_sites_mono (by have h := hs (Nat.le_succ i); change s i ≤ s (i + 1) at h; omega) (ih x hx)
    · exact box_sites_mono (by have h := ha (i + 1); omega) (Finset.mem_toList.mp hx)

end
end FiniteAvalanches.Wilson.Lattice.PaddedHistoryLocalization
