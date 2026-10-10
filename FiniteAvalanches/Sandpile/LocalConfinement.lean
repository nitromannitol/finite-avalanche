import FiniteAvalanches.Sandpile.WiredTermination

/-! The local boundary test for a confined one-grain avalanche. -/

namespace FiniteAvalanches.Sandpile

open LatticeProb LatticeProb.Sandpile FiniteAvalanches
open scoped Classical

noncomputable section

theorem box_sites_mono {R S : ℕ} (h : R ≤ S) : boxSites R ⊆ boxSites S := by
  intro x hx
  rw [mem_box_sites] at hx ⊢
  intro i
  have hi := hx i
  constructor <;> omega

theorem box_sites_add_unit {R : ℕ} {x : Site2} (hx : x ∈ boxSites R) (i : Fin 2) :
    x + unit i ∈ boxSites (R + 1) := by
  rw [mem_box_sites] at hx ⊢
  intro j
  have hj := hx j
  by_cases h : j = i
  · subst j; simpa [unit] using (show -(↑(R + 1) : ℤ) ≤ x i + 1 ∧ x i + 1 ≤ ↑(R + 1) by omega)
  · simp [unit, h]
    constructor <;> omega

theorem box_sites_sub_unit {R : ℕ} {x : Site2} (hx : x ∈ boxSites R) (i : Fin 2) :
    x - unit i ∈ boxSites (R + 1) := by
  rw [mem_box_sites] at hx ⊢
  intro j
  have hj := hx j
  by_cases h : j = i
  · subst j; simpa [unit] using (show -(↑(R + 1) : ℤ) ≤ x i - 1 ∧ x i - 1 ≤ ↑(R + 1) by omega)
  · simp [unit, h]
    constructor <;> omega

theorem list_counts_support_subset {R : ℕ} {w : List Site2}
    (hwR : ∀ x ∈ w, x ∈ boxSites R) : (listCounts w).support ⊆ boxSites R := by
  rw [listCounts_support]
  exact fun _ hx => hwR _ (List.mem_toFinset.mp hx)

theorem affected_subset_box_succ {R : ℕ} {ξ u : Counts}
    (hξ : ξ.support ⊆ boxSites R) (hu : u.support ⊆ boxSites R) :
    affected ξ u ⊆ boxSites (R + 1) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · exact box_sites_mono (Nat.le_succ R) (hξ hx)
    · exact box_sites_mono (Nat.le_succ R) (hu hx)
  · obtain ⟨y, hy, hx⟩ := Finset.mem_biUnion.mp hx
    simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨i, rfl | rfl⟩ := hx
    · exact box_sites_add_unit (hu hy) i
    · exact box_sites_sub_unit (hu hy) i

/-- Check the original heights plus the recorded outgoing chips on the exterior layer. -/
def boundary_passes (η : StableField) (o : Site2) (R : ℕ) (w : List Site2) : Prop :=
  ∀ x ∈ boxSites (R + 1), x ∉ boxSites R →
    initial η (oneGrain o) x + lap (fun y => (listCounts w y : ℤ)) x < 4

theorem one_grain_support_subset_box {R : ℕ} {o : Site2} (ho : o ∈ boxSites R) :
    (oneGrain o).support ⊆ boxSites R := by
  exact Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.mpr ho)

theorem stabilizes_iff_boundary_passes {η : StableField} {o : Site2} {R : ℕ}
    {w : List Site2} (ho : o ∈ boxSites R)
    (hw : WiredStabilizes η (oneGrain o) (boxSites R) w) :
    Stabilizes η (oneGrain o) w ↔ boundary_passes η o R w := by
  constructor
  · exact fun h x _ _ => (h.2 x).2
  · intro hb
    rw [stabilizes_iff_legal_and_lt]
    refine ⟨hw.2.1, ?_⟩
    intro x
    by_cases hx : x ∈ boxSites R
    · exact (hw.2.2 x hx).2
    · by_cases hx' : x ∈ boxSites (R + 1)
      · exact hb x hx' hx
      · have ha : x ∉ affected (oneGrain o) (listCounts w) := fun h => hx'
          (affected_subset_box_succ (one_grain_support_subset_box ho)
            (list_counts_support_subset hw.1) h)
        rw [lap_zero_outside_affected ha]
        have hz := (count_zero_outside_affected ha).1
        simp only [initial, hz, Nat.cast_zero, add_zero]
        exact_mod_cast (η x).isLt

theorem boundary_passes_iff_of_wired_stabilizes {η : StableField} {o : Site2} {R : ℕ}
    {w v : List Site2}
    (hw : WiredStabilizes η (oneGrain o) (boxSites R) w)
    (hv : WiredStabilizes η (oneGrain o) (boxSites R) v) :
    boundary_passes η o R w ↔ boundary_passes η o R v := by
  unfold boundary_passes
  rw [wiredStabilizes_counts_unique hw hv]

/-- A literal finite legal stabilization whose toppled vertices stay in the box. -/
def confined_stabilizes (η : StableField) (o : Site2) (R : ℕ) : Prop :=
  ∃ w : List Site2, Stabilizes η (oneGrain o) w ∧ ∀ x ∈ w, x ∈ boxSites R

theorem confined_stabilizes_iff_boundary_passes {η : StableField} {o : Site2} {R : ℕ}
    {w : List Site2} (ho : o ∈ boxSites R)
    (hw : WiredStabilizes η (oneGrain o) (boxSites R) w) :
    confined_stabilizes η o R ↔ boundary_passes η o R w := by
  constructor
  · rintro ⟨v, hv, hvR⟩
    have hv' : WiredStabilizes η (oneGrain o) (boxSites R) v :=
      ⟨hvR, hv.1, fun x _ => hv.2 x⟩
    exact (boundary_passes_iff_of_wired_stabilizes hv' hw).mp
      ((stabilizes_iff_boundary_passes ho hv').mp hv)
  · intro hb
    exact ⟨w, (stabilizes_iff_boundary_passes ho hw).mpr hb, hw.1⟩

theorem wired_stabilizes_of_agree {η η' : StableField} {ξ : Counts} {V : Finset Site2}
    {w : List Site2} (hw : WiredStabilizes η ξ V w)
    (heq : ∀ x ∈ V, η' x = η x) : WiredStabilizes η' ξ V w := by
  refine ⟨hw.1, ?_, ?_⟩
  · intro k hk
    simpa only [initial, heq w[k] (hw.1 _ (List.getElem_mem hk))] using hw.2.1 k hk
  · intro x hx
    simpa only [initial, heq x hx] using hw.2.2 x hx

theorem confined_stabilizes_iff_of_agree {η η' : StableField} {o : Site2} {R : ℕ}
    (ho : o ∈ boxSites R) (heq : ∀ x ∈ boxSites (R + 1), η' x = η x) :
    confined_stabilizes η' o R ↔ confined_stabilizes η o R := by
  obtain ⟨w, hw⟩ := exists_wired_stabilizes η (oneGrain o) R
  have hw' := wired_stabilizes_of_agree hw
    (fun x hx => heq x (box_sites_mono (Nat.le_succ R) hx))
  rw [confined_stabilizes_iff_boundary_passes ho hw', confined_stabilizes_iff_boundary_passes ho hw]
  unfold boundary_passes
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  simp only [initial, heq x hx]

theorem site_radius_zero_le_iff (x : Site2) (R : ℕ) :
    siteRadius 0 x ≤ R ↔ x ∈ boxSites R := by
  rw [siteRadius_le_iff, mem_box_sites]
  simp only [Pi.zero_apply, sub_zero, abs_le, FiniteWired.inBox]

theorem radius_le_iff_confined_stabilizes (η : StableField) (R : ℕ) :
    radius η 0 ≤ (R : WithTop ℕ) ↔ confined_stabilizes η 0 R := by
  constructor
  · intro hr
    have hf : FiniteStabilizable η 0 := by
      by_contra hn
      rw [(radius_eq_top_iff η 0).mpr hn] at hr
      simp at hr
    obtain ⟨w, hw⟩ := hf
    rw [radius_of_stabilizes hw] at hr
    have hr : countsRadius 0 (listCounts w) ≤ R := WithTop.coe_le_coe.mp hr
    refine ⟨w, hw, ?_⟩
    intro x hx
    apply (site_radius_zero_le_iff x R).mp
    apply (countsRadius_le_iff 0 (listCounts w) R).mp hr x
    rw [listCounts_apply]
    exact List.count_pos_iff.mpr hx
  · rintro ⟨w, hw, hwR⟩
    rw [radius_of_stabilizes hw]
    apply WithTop.coe_le_coe.mpr
    change countsRadius 0 (listCounts w) ≤ R
    apply (countsRadius_le_iff 0 (listCounts w) R).mpr
    intro x hx
    apply (site_radius_zero_le_iff x R).mpr
    exact hwR x (List.count_pos_iff.mp (by simpa only [listCounts_apply] using hx))

theorem radius_le_iff_of_agree {η η' : StableField} (R : ℕ)
    (heq : ∀ x ∈ boxSites (R + 1), η' x = η x) :
    radius η' 0 ≤ (R : WithTop ℕ) ↔ radius η 0 ≤ (R : WithTop ℕ) := by
  rw [radius_le_iff_confined_stabilizes, radius_le_iff_confined_stabilizes]
  apply confined_stabilizes_iff_of_agree _ heq
  rw [mem_box_sites]
  exact fun _ => ⟨by simp, by simp⟩

theorem confined_stabilization_counts_independent {η η' : StableField} {o : Site2}
    {R : ℕ} {w : List Site2} (ho : o ∈ boxSites R)
    (hw : Stabilizes η (oneGrain o) w) (hwR : ∀ x ∈ w, x ∈ boxSites R)
    (heq : ∀ x ∈ boxSites (R + 1), η' x = η x) :
    Stabilizes η' (oneGrain o) w ∧
      ∀ N : ℕ, R + 1 ≤ N → ∀ v : List Site2,
        WiredStabilizes η' (oneGrain o) (boxSites N) v → listCounts v = listCounts w := by
  have ha := affected_subset_box_succ (one_grain_support_subset_box ho)
    (list_counts_support_subset hwR)
  have hf := finite_determination_counts hw (fun x hx => heq x (ha hx))
  refine ⟨hf.1.1, ?_⟩
  intro N hN v hv
  exact (hf.2 (boxSites N) (ha.trans (box_sites_mono hN))).2 v hv

theorem confined_stabilizes_iff_wired_support {η : StableField} {o : Site2}
    {R N : ℕ} (ho : o ∈ boxSites R) (hN : R + 1 ≤ N) :
    confined_stabilizes η o R ↔ ∃ w : List Site2,
      WiredStabilizes η (oneGrain o) (boxSites N) w ∧
      (listCounts w).support ⊆ boxSites R := by
  constructor
  · rintro ⟨w, hw, hwR⟩
    refine ⟨w, ⟨fun x hx => box_sites_mono (by omega) (hwR x hx),
      hw.1, fun x _ => hw.2 x⟩, list_counts_support_subset hwR⟩
  · rintro ⟨w, hw, hu⟩
    have ha := affected_subset_box_succ (one_grain_support_subset_box ho) hu
    have hglobal : Stabilizes η (oneGrain o) w := by
      rw [stabilizes_iff_legal_and_lt]
      refine ⟨hw.2.1, ?_⟩
      intro x
      by_cases hx : x ∈ boxSites N
      · exact (hw.2.2 x hx).2
      · have hx' : x ∉ affected (oneGrain o) (listCounts w) :=
          fun h => hx (box_sites_mono hN (ha h))
        rw [lap_zero_outside_affected hx']
        have hz := (count_zero_outside_affected hx').1
        simp only [initial, hz, Nat.cast_zero, add_zero]
        exact_mod_cast (η x).isLt
    refine ⟨w, hglobal, ?_⟩
    intro x hx
    exact hu (by rw [listCounts_support]; exact List.mem_toFinset.mpr hx)


end
end FiniteAvalanches.Sandpile
