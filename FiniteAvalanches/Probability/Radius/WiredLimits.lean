import FiniteAvalanches.Probability.Radius.Tails
import FiniteAvalanches.Sandpile.Waves.RadiusEvents

/-! Direct passage from the original normalized wired fired-support events to the
literal limit radius. Sources stay arbitrary; a cofinal volume sequence contains
all determining coordinates by construction. No translation law or finite bound
is supplied by these supporting results. -/
namespace FiniteAvalanches.Probability
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

theorem source_in_shifted_volume (o : Site2) (R k : ℕ) :
    FiniteWired.inBox (k + (siteRadius 0 o + R + 1)) o :=
  (mem_box_sites _ _).mp ((site_radius_zero_le_iff o _).mp (by omega))

theorem tendsto_wired_radius_tail_of_weak
    (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ)) (o : Site2) (R : ℕ) :
    Tendsto (fun k : ℕ =>
      let N := k + (siteRadius 0 o + R + 1)
      let a := FiniteWired.activeOfSite N o (source_in_shifted_volume o R k)
      FiniteWired.law N {η | finiteAvalancheLeaves a
        ((boxSites R).image (fun y => y + o)) η}) atTop
      (nhds ((μ : Measure StableField) {η | (R : WithTop ℕ) < radius η o})) := by
  have h := (tendsto_radius_gt_of_weak μ hμ o R).comp
    (tendsto_add_atTop_nat (siteRadius 0 o + R + 1))
  apply h.congr'
  filter_upwards [] with k
  exact finiteFieldLaw_radius_tail_eq_wired
    (FiniteWired.activeOfSite _ o (source_in_shifted_volume o R k)) R (by
      rw [FiniteWired.site_activeOfSite]
      omega)

theorem radius_tail_le_of_wired_bounds
    (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ)) (o : Site2) (R : ℕ) (b : ℝ≥0∞)
    (hB : ∀ᶠ k : ℕ in atTop,
      let N := k + (siteRadius 0 o + R + 1)
      let a := FiniteWired.activeOfSite N o (source_in_shifted_volume o R k)
      FiniteWired.law N {η | finiteAvalancheLeaves a
        ((boxSites R).image (fun y => y + o)) η} ≤ b) :
    (μ : Measure StableField) {η | (R : WithTop ℕ) < radius η o} ≤ b :=
  le_of_tendsto (tendsto_wired_radius_tail_of_weak μ hμ o R) hB

theorem ae_all_finiteStabilizable_of_wired_tail_bounds
    (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ))
    (b : ℕ → ℝ≥0∞) (hb : Tendsto b atTop (nhds 0))
    (hB : ∀ (o : Site2) (R : ℕ), ∀ᶠ k : ℕ in atTop,
      let N := k + (siteRadius 0 o + R + 1)
      let a := FiniteWired.activeOfSite N o (source_in_shifted_volume o R k)
      FiniteWired.law N {η | finiteAvalancheLeaves a
        ((boxSites R).image (fun y => y + o)) η} ≤ b R) :
    ∀ᵐ η ∂(μ : Measure StableField), ∀ o : Site2, FiniteStabilizable η o :=
  ae_all_finiteStabilizable_of_radius_tail_bounds (μ : Measure StableField)
    (fun _ => b) (fun _ => hb) (fun o R => radius_tail_le_of_wired_bounds μ hμ o R (b R) (hB o R))

theorem tendsto_origin_wired_radius_tail_of_weak
    (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ)) (R : ℕ) :
    Tendsto (fun N : ℕ =>
      let a : FiniteWired.Active N := fun _ => ⟨0, by constructor <;> omega⟩
      FiniteWired.law N {η | finiteAvalancheLeaves a (boxSites R) η}) atTop
      (nhds ((μ : Measure StableField) {η | (R : WithTop ℕ) < radius η 0})) := by
  apply (tendsto_radius_gt_of_weak μ hμ 0 R).congr'
  filter_upwards [eventually_ge_atTop (R + 1)] with N hN
  let a : FiniteWired.Active N := fun _ => ⟨0, by constructor <;> omega⟩
  have ha : FiniteWired.site a = 0 := rfl
  have hr0 : siteRadius 0 (FiniteWired.site a) = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [siteRadius_le_iff, ha]
    simp
  have he := finiteFieldLaw_radius_tail_eq_wired a R
    (by rw [hr0]; simpa only [zero_add] using hN)
  have hb : (boxSites R).image (fun y => y + FiniteWired.site a) = boxSites R := by
    simp [ha]
  rw [hb, ha] at he
  exact he

end
end FiniteAvalanches.Probability
