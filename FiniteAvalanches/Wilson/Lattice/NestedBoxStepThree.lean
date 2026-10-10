import FiniteAvalanches.Wilson.Lattice.DistinctStartLocalization
import FiniteAvalanches.Wilson.Lattice.ReciprocalStepThree
import FiniteAvalanches.Wilson.Lattice.LocalizationUnion

/-! Exact escape control for concatenated nested box prefixes. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.NestedBoxStepThree
open LatticeProb MeasureTheory FiniteAvalanches Sandpile
open ActualQueryPrefixes ActualLocalizationUnion ReciprocalStepThree
open scoped Classical ENNReal
noncomputable section

/-- Any list of starts in the source box has the same universal escape estimate,
including repeated starts and all terminal vertices of the original full history. -/
theorem box_list_history_escape : ∃ D : ℝ, 0 < D ∧
    ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected → (0 : Site 2) ∈ K →
    ∀ R : RootPair, (K : Set (Site 2)) ⊆ R.zero →
    ∀ r : ℕ, 2 ≤ r →
      16 * r ^ 6 ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
    ∀ L : List (Site 2), (∀ x ∈ L, x ∈ boxSites (3 * r + 1)) →
      wilsonRows (prefixExit R L (r ^ 6)) ≤
        ENNReal.ofReal (D * (r : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨D, hD, hbound⟩ := DistinctStartLocalization.finite_stopped_history_distinct_bound
  refine ⟨128 * D, mul_pos (by norm_num) hD, ?_⟩
  intro K hK h0 R hKR r hr hdiam L hL
  have hmargin := sixth_power_margin r hr
  have hboundary : ∃ z ∈ K, siteRadius 0 z = r ^ 6 - 1 :=
    connected_boundary_of_diameter K hK.preconnected h0 (r ^ 6 - 1) (by omega) (by omega)
  have hqueries : ∀ x ∈ L, siteRadius 0 x ≤ 3 * r + 1 :=
    fun x hx => (site_radius_zero_le_iff x _).mpr (hL x hx)
  have hb := hbound (K : Set (Site 2)) hK.preconnected h0 R hKR
    (3 * r + 1) (r ^ 6) (sixth_power_margin r hr) hboundary L hqueries
  have hc : L.toFinset.card ≤ (6 * r + 3) ^ 2 := by
    calc
      _ ≤ (boxSites (3 * r + 1)).card := Finset.card_le_card (by
        intro x hx
        exact hL x (List.mem_toFinset.mp hx))
      _ = (6 * r + 3) ^ 2 := by rw [← Finset.length_toList, query_list_length]
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hc' : (L.toFinset.card : ℝ) ≤ (6 * (r : ℝ) + 3) ^ 2 := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc' hD.le) (Real.sqrt_nonneg (((3 * r + 1 + 1 : ℕ) : ℝ) / r ^ 6))
  have hs := query_sixth_power_bound_mul D (r : ℝ) hD.le (by exact_mod_cast hr)
  push_cast at hm
  rw [show (3 : ℝ) * r + 1 + 1 = 3 * r + 2 by ring] at hm
  push_cast
  rw [show (3 : ℝ) * r + 1 + 1 = 3 * r + 2 by ring]
  exact hm.trans hs


/-- The union of all completed nested box queries is exactly the last box. -/
theorem queryPrefix_box_toFinset (r : ℕ → ℕ) (hmono : Monotone r) (i : ℕ) :
    (queryPrefix (fun j => (boxSites (3 * r j + 1)).toList) (i + 1)).toFinset =
      boxSites (3 * r i + 1) := by
  induction i with
  | zero => simp only [queryPrefix, List.nil_append, Finset.toList_toFinset]
  | succ i ih =>
    rw [queryPrefix, List.toFinset_append, ih, Finset.toList_toFinset]
    exact Finset.union_eq_right.mpr (box_sites_mono (by
      have hi : r i ≤ r (i + 1) := hmono (Nat.le_succ i)
      omega))

/-- The distinct-start count of the actual concatenated prefix is the source square count. -/
theorem queryPrefix_box_card (r : ℕ → ℕ) (hmono : Monotone r) (i : ℕ) :
    (queryPrefix (fun j => (boxSites (3 * r j + 1)).toList) (i + 1)).toFinset.card =
      (6 * r i + 3) ^ 2 := by
  rw [queryPrefix_box_toFinset r hmono i, ← Finset.length_toList, query_list_length]

/-- One positive constant precedes the obstacle, roots, schedule and index.
The event is the original concatenated sampler prefix, with every terminal vertex. -/
theorem nested_prefix_history_escape : ∃ D : ℝ, 0 < D ∧
    ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected → (0 : Site 2) ∈ K →
    ∀ R : RootPair, (K : Set (Site 2)) ⊆ R.zero →
    ∀ r : ℕ → ℕ, Monotone r →
    ∀ i : ℕ, 2 ≤ r i →
      16 * (r i) ^ 6 ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      wilsonRows (prefixExit R
        (queryPrefix (fun j => (boxSites (3 * r j + 1)).toList) (i + 1)) ((r i) ^ 6)) ≤
        ENNReal.ofReal (D * (r i : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨D, hD, hbound⟩ := box_list_history_escape
  refine ⟨D, hD, ?_⟩
  intro K hK h0 R hKR r hmono i hr hdiam
  apply hbound K hK h0 R hKR (r i) hr hdiam
  intro x hx
  rw [← queryPrefix_box_toFinset r hmono i]
  exact List.mem_toFinset.mpr hx

end
end FiniteAvalanches.Wilson.Lattice.NestedBoxStepThree
