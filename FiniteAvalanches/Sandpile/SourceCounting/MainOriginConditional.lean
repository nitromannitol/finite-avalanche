import FiniteAvalanches.Sandpile.SourceCounting.UniformReciprocalBound
import FiniteAvalanches.Probability.MainScalarScale
import FiniteAvalanches.Paper.RevisionB972.FiniteLimsupStatement
import FiniteAvalanches.Probability.MainTailAssembly

/-! Ordinary conditional assembly of the exact current origin conclusion.
The literal closed forest reciprocal estimate remains an open predecessor. -/
namespace FiniteAvalanches.ConditioningMain
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory Filter
open FiniteAvalanches.External.SandpileLimit
open FiniteAvalanches.Wilson.Lattice TreeMeasurability11
open FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Probability FiniteAvalanches.Probability.MainTailTransfer
open scoped Classical ENNReal
noncomputable section

/-- Eventual uniform finite-volume upper bounds pass to the actual finite limsup. -/
theorem internal_finiteZN_limsup_le (r : ℕ) (B : ℝ)
    (hB : ∀ N : ℕ, r ≤ N →
      (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t
        ∂WiredTrees.law N) ≤ B) :
    Filter.limsup (fun N : ℕ =>
      ∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t
        ∂WiredTrees.law N) atTop ≤ B := by
  apply limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (x := (0 : ℝ)) ?_)
  · exact (eventually_ge_atTop r).mono fun N hN => hB N hN
  · intro N
    apply integral_nonneg
    intro t
    exact (ReciprocalLimit15.finiteZN_bounds N (sourceMarks r)
      (Finset.insert_nonempty _ _) t).1

/-- The sole substantive input is the literal closed current forest estimate.
The conclusion is the exact current MainOrigin conjunction. -/
theorem internal_main_origin_of_closed_forest_bound
    (hforest : ∃ a C : ℝ, 0 < a ∧ ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      ∀ γ : SimpleRay, Disjoint (K : Set (Site 2)) γ.vertices →
        (∃ k ∈ K, (lattice 2).Adj k (γ.vertex 0)) →
        ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ.vertices →
          (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
            C * Real.rpow
              (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
              (-a)) :
    (∀ᵐ η ∂(infiniteVolumeLaw : Measure StableField),
      ∃ w : List Site2, Stabilizes η (oneGrain (0 : Site2)) w) ∧
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ,
      ∀ R : ℝ, 0 ≤ R →
        (infiniteVolumeLaw : Measure StableField).real
          {η | ENNReal.ofReal R < extendedCount (radius η (0 : Site2))} ≤
        C * Real.rpow (Real.log (R + 2)) (-a) := by
  obtain ⟨a, C, ha, hfinite⟩ :=
    ConditioningConsumer.source_marks_uniform_finiteZN_bound_of_closed_forest_bound hforest
  obtain ⟨E, hreduce⟩ := Paper.RevisionB972.reciprocal_reduction_limsup_v2
  let D : ℝ := max C 0 * (6 : ℝ) ^ a + max E 0 * (2 : ℝ) ^ (1 / 3 : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have heventual : ∀ᶠ M : ℕ in atTop,
      (infiniteVolumeLaw : Measure StableField).real
          {η | ENNReal.ofReal (M : ℝ) < extendedCount (radius η 0)} ≤
        D * Real.log ((M : ℝ) + 2) ^ (-a) := by
    filter_upwards [internal_sixth_root_scale a ha] with M hscale
    let r : ℕ := ⌊((M : ℝ) + 2) ^ (1 / 6 : ℝ)⌋₊
    obtain ⟨hr, hrM, hlog, herror⟩ := hscale
    have hlim := internal_finiteZN_limsup_le r
      (C * Real.log ((r : ℝ) + 2) ^ (-a)) (hfinite r hr)
    have hlognonneg : 0 ≤ Real.log ((r : ℝ) + 2) ^ (-a) :=
      Real.rpow_nonneg (Real.log_nonneg (by
        have := Nat.cast_nonneg (α := ℝ) r
        linarith)) _
    have hdiffnonneg : 0 ≤ (r : ℝ) * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (sub_nonneg.mpr
        (by exact_mod_cast (show r ≤ M from by omega))) _)
    calc
      _ ≤ C * Real.log ((r : ℝ) + 2) ^ (-a) +
          E * (r : ℝ) * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) :=
        (hreduce r hr M hrM).trans (add_le_add hlim le_rfl)
      _ ≤ max C 0 * ((6 : ℝ) ^ a * Real.log ((M : ℝ) + 2) ^ (-a)) +
          max E 0 * ((2 : ℝ) ^ (1 / 3 : ℝ) * Real.log ((M : ℝ) + 2) ^ (-a)) := by
        rw [mul_assoc E]
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_right (le_max_left C 0) hlognonneg).trans
            (mul_le_mul_of_nonneg_left hlog (le_max_right C 0))
        · exact (mul_le_mul_of_nonneg_right (le_max_left E 0) hdiffnonneg).trans
            (mul_le_mul_of_nonneg_left herror (le_max_right E 0))
      _ = _ := by dsimp [D]; ring
  obtain ⟨K, hK⟩ := eventually_atTop.mp heventual
  let F : ℝ := D + Real.log ((K : ℝ) + 2) ^ a
  have hF : 0 ≤ F := by
    have hlogK : 0 ≤ Real.log ((K : ℝ) + 2) := Real.log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) K
      linarith)
    exact add_nonneg hD (Real.rpow_nonneg hlogK _)
  have hnat : ∀ M : ℕ,
      (infiniteVolumeLaw : Measure StableField)
          {η | (M : WithTop ℕ) < radius η 0} ≤
        ENNReal.ofReal (F * Real.log ((M : ℝ) + 2) ^ (-a)) := by
    intro M
    have hlog : 0 < Real.log ((M : ℝ) + 2) := Real.log_pos (by
      have := Nat.cast_nonneg (α := ℝ) M
      linarith)
    have hFM : 0 ≤ F * Real.log ((M : ℝ) + 2) ^ (-a) :=
      mul_nonneg hF (Real.rpow_nonneg hlog.le _)
    have hreal : (infiniteVolumeLaw : Measure StableField).real
          {η | ENNReal.ofReal (M : ℝ) < extendedCount (radius η 0)} ≤
        F * Real.log ((M : ℝ) + 2) ^ (-a) := by
      by_cases hlarge : K ≤ M
      · apply (hK M hlarge).trans
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlog.le _)
        dsimp [F]
        have hn := Real.rpow_nonneg
          (Real.log_nonneg (show (1 : ℝ) ≤ (K : ℝ) + 2 by
            have := Nat.cast_nonneg (α := ℝ) K
            linarith)) a
        linarith only [hn]
      · have hlogle : Real.log ((M : ℝ) + 2) ^ a ≤ Real.log ((K : ℝ) + 2) ^ a := by
          apply Real.rpow_le_rpow hlog.le _ ha.le
          apply Real.log_le_log (by positivity)
          have hMK : (M : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show M ≤ K by omega)
          linarith only [hMK]
        have hprod : 1 ≤ Real.log ((K : ℝ) + 2) ^ a * Real.log ((M : ℝ) + 2) ^ (-a) := by
          calc
            1 = Real.log ((M : ℝ) + 2) ^ a * Real.log ((M : ℝ) + 2) ^ (-a) := by
              rw [← Real.rpow_add hlog, add_neg_cancel, Real.rpow_zero]
            _ ≤ _ := mul_le_mul_of_nonneg_right hlogle (Real.rpow_nonneg hlog.le _)
        apply (show (infiniteVolumeLaw : Measure StableField).real
          {η | ENNReal.ofReal (M : ℝ) < extendedCount (radius η 0)} ≤ 1 from by
            exact ENNReal.toReal_mono (by norm_num)
              (prob_le_one (μ := (infiniteVolumeLaw : Measure StableField)))).trans
        apply hprod.trans
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlog.le _)
        dsimp [F]
        linarith only [hD]
    rw [Measure.real, real_radius_tail_eq_floor 0 (M : ℝ) (Nat.cast_nonneg _),
      Nat.floor_natCast] at hreal
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hFM).mpr hreal
  have hreal := internal_real_radius_tail_of_nat_tail
    (infiniteVolumeLaw : Measure StableField) a F ha hF hnat
  constructor
  · exact ae_finiteStabilizable_of_radius_tail_bound
      (infiniteVolumeLaw : Measure StableField) 0
      (fun M => ENNReal.ofReal (F * Real.log ((M : ℝ) + 2) ^ (-a)))
      ((internal_log_tail_tendsto_zero a F ha).comp tendsto_natCast_atTop_atTop) hnat
  · refine ⟨a, ha, F * (2 : ℝ) ^ a, ?_⟩
    intro R hR
    exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (mul_nonneg hF (by positivity))
        (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)) (hreal R hR)

end
end FiniteAvalanches.ConditioningMain
