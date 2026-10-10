import FiniteAvalanches.Sandpile.RadiusLocality
import FiniteAvalanches.Probability.Radius.Cylinders
import FiniteAvalanches.Sandpile.Waves.AvalancheEvents

/-! The actual radius cylinder agrees with the actual wired fired-support event
once its determining coordinates are inside the finite volume. Wired termination
supplies a legal list before comparison; no global stabilization is assumed. -/
namespace FiniteAvalanches.Sandpile
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical
noncomputable section

theorem mem_translated_box_iff (o x : Site2) (R : ℕ) :
    x ∈ (boxSites R).image (fun y => y + o) ↔ siteRadius o x ≤ R := by
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [siteRadius_le_iff, mem_box_sites] at *
    intro i
    simpa only [Pi.add_apply, add_sub_cancel_right, abs_le] using hy i
  · intro hx
    refine Finset.mem_image.mpr ⟨x - o, ?_, sub_add_cancel x o⟩
    rw [mem_box_sites]
    exact fun i => abs_le.mp ((siteRadius_le_iff o x R).mp hx i)

theorem counts_radius_le_iff_translated_support (o : Site2) (u : Counts) (R : ℕ) :
    countsRadius o u ≤ R ↔ u.support ⊆ (boxSites R).image (fun y => y + o) := by
  rw [countsRadius_le_iff]
  constructor
  · intro h x hx
    exact (mem_translated_box_iff o x R).mpr (h x (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)))
  · intro h x hx
    exact (mem_translated_box_iff o x R).mp (h (Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hx)))

theorem radius_le_iff_wired_counts {η : StableField} {o : Site2} {R N : ℕ}
    (hN : siteRadius 0 o + R + 1 ≤ N) {w : List Site2}
    (hw : WiredStabilizes η (oneGrain o) (boxSites N) w) :
    radius η o ≤ (R : WithTop ℕ) ↔ countsRadius o (listCounts w) ≤ R := by
  constructor
  · intro hr
    have hf : FiniteStabilizable η o := by
      by_contra hn
      rw [(radius_eq_top_iff η o).mpr hn] at hr
      simp at hr
    obtain ⟨v, hv⟩ := hf
    rw [radius_of_stabilizes hv] at hr
    have hvr := (countsRadius_le_iff o (listCounts v) R).mp (WithTop.coe_le_coe.mp hr)
    have hvN : ∀ x ∈ v, x ∈ boxSites N := by
      intro x hx
      apply box_sites_mono (by omega) (mem_box_of_site_radius_le (hvr x _))
      rw [listCounts_apply]
      exact List.count_pos_iff.mpr hx
    have hv' : WiredStabilizes η (oneGrain o) (boxSites N) v :=
      ⟨hvN, hv.1, fun x _ => hv.2 x⟩
    rw [wiredStabilizes_counts_unique hw hv']
    exact WithTop.coe_le_coe.mp hr
  · intro hr
    have hu : (listCounts w).support ⊆ boxSites (siteRadius 0 o + R) := by
      intro x hx
      exact mem_box_of_site_radius_le
        ((countsRadius_le_iff o (listCounts w) R).mp hr x
          (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)))
    have ho : o ∈ boxSites (siteRadius 0 o + R) :=
      (site_radius_zero_le_iff o _).mp (Nat.le_add_right _ _)
    have ha := (affected_subset_box_succ (one_grain_support_subset_box ho) hu).trans
      (box_sites_mono hN)
    have hg : Stabilizes η (oneGrain o) w := by
      rw [stabilizes_iff_legal_and_lt]
      refine ⟨hw.2.1, ?_⟩
      intro x
      by_cases hx : x ∈ boxSites N
      · exact (hw.2.2 x hx).2
      · have hx' : x ∉ affected (oneGrain o) (listCounts w) := fun h => hx (ha h)
        rw [lap_zero_outside_affected hx']
        have hz := (count_zero_outside_affected hx').1
        simp only [initial, hz, Nat.cast_zero, add_zero]
        exact_mod_cast (η x).isLt
    rw [radius_of_stabilizes hg]
    exact WithTop.coe_le_coe.mpr hr

theorem finite_avalanche_leaves_iff_radius_gt {N : ℕ} (o : FiniteWired.Active N)
    (R : ℕ) (hN : siteRadius 0 (FiniteWired.site o) + R + 1 ≤ N)
    (η : FiniteWired.Recurrent N) :
    finiteAvalancheLeaves o ((boxSites R).image (fun y => y + FiniteWired.site o)) η ↔
      (R : WithTop ℕ) < radius (FiniteWired.zeroExtend N η) (FiniteWired.site o) := by
  obtain ⟨v, hv⟩ := exists_wired_stabilizes (FiniteWired.zeroExtend N η)
    (oneGrain (FiniteWired.site o)) N
  constructor
  · rintro ⟨w, hw, hn⟩
    rw [← not_le, radius_le_iff_wired_counts hN hw,
      counts_radius_le_iff_translated_support]
    exact hn
  · intro hr
    refine ⟨v, hv, ?_⟩
    rw [← counts_radius_le_iff_translated_support, ← radius_le_iff_wired_counts hN hv]
    exact not_le.mpr hr

theorem finiteFieldLaw_radius_tail_eq_wired {N : ℕ} (o : FiniteWired.Active N)
    (R : ℕ) (hN : siteRadius 0 (FiniteWired.site o) + R + 1 ≤ N) :
    FiniteWired.finiteFieldLaw N {η | (R : WithTop ℕ) < radius η (FiniteWired.site o)} =
      FiniteWired.law N {η | finiteAvalancheLeaves o
        ((boxSites R).image (fun y => y + FiniteWired.site o)) η} := by
  rw [FiniteWired.finiteFieldLaw, Measure.map_apply (FiniteWired.zeroExtend_measurable N)
    (FiniteAvalanches.Probability.measurableSet_radius_gt_local (FiniteWired.site o) R)]
  congr 1
  ext η
  exact (finite_avalanche_leaves_iff_radius_gt o R hN η).symm

end
end FiniteAvalanches.Sandpile
