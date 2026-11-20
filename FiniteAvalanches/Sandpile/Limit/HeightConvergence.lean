import FiniteAvalanches.Sandpile.Limit.PastConvergence

/-! Along any exhaustion of `ℤ²`, the finite-volume probability of prescribed heights on a
nonempty finite set `B` converges to the mixture of the inner ratios over the limiting
past events of `B`. -/

set_option autoImplicit false

namespace FiniteAvalanches.Sandpile.InfiniteVolume

open LatticeProb MeasureTheory Filter Topology FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.Lattice.SiteRoots FiniteAvalanches.Sandpile.GammaGraph
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal

noncomputable section

variable {Λ : ℕ → Finset Site2} (hΛ : IsExhaustion Λ)

theorem innerRatio_le_one (B S : Finset Site2) (ξ : Site2 → ℕ) : innerRatio B S ξ ≤ 1 := by
  rw [innerRatio]
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  exact_mod_cast latticeInnerValues_card_le B S ξ

theorem innerRatio_ne_top (B S : Finset Site2) (ξ : Site2 → ℕ) : innerRatio B S ξ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (innerRatio_le_one B S ξ)

/-- The real inner ratio. -/
abbrev ratio (B S : Finset Site2) (ξ : Site2 → ℕ) : ℝ := (innerRatio B S ξ).toReal

theorem ratio_nonneg (B S : Finset Site2) (ξ : Site2 → ℕ) : 0 ≤ ratio B S ξ := ENNReal.toReal_nonneg

theorem ratio_le_one (B S : Finset Site2) (ξ : Site2 → ℕ) : ratio B S ξ ≤ 1 := by
  rw [ratio, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (innerRatio_le_one B S ξ)

/-- The limiting probability of prescribed heights on `B`. -/
def heightLimit (B : Finset Site2) (ξ : Site2 → ℕ) : ℝ :=
  ∑' S : Finset Site2, (pastWeight B S).toReal * ratio B S ξ

theorem summable_weight_ratio {B : Finset Site2} (hB : B.Nonempty) (ξ : Site2 → ℕ) :
    Summable fun S : Finset Site2 => (pastWeight B S).toReal * ratio B S ξ :=
  Summable.of_nonneg_of_le (fun S => mul_nonneg ENNReal.toReal_nonneg (ratio_nonneg B S ξ))
    (fun S => mul_le_of_le_one_right ENNReal.toReal_nonneg (ratio_le_one B S ξ))
    (hasSum_pastWeight_toReal hB).summable

/-- The past laws over all subsets of the volume add up to one. -/
theorem sum_pastProb_volume (B : Finset Site2) (n : ℕ) :
    ∑ S ∈ (Λ n).powerset, pastProb Λ B S n = 1 := by
  have hdisj : (⋃ S ∈ (Λ n).powerset, {t : (graph (Λ n)).SpanningTree |
      pastSites (Λ n) B t = S}) = Set.univ := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_powerset, exists_prop,
      Set.mem_univ, iff_true]
    exact ⟨_, sitesOf_subset _ _, rfl⟩
  rw [← measure_univ (μ := (graph (Λ n)).treeLaw), ← hdisj, measure_biUnion_finset]
  · intro S _ S' _ hne
    exact Set.disjoint_left.mpr fun t h1 h2 => hne (h1.symm.trans h2)
  · exact fun _ _ => measurableSet_setOf.mpr (measurable_of_countable _)

theorem eventually_heightEvent_eq (B : Finset Site2) (ξ : Site2 → ℕ) (hB : ∀ᶠ n in atTop, B ⊆ Λ n) :
    ∀ᶠ n in atTop, (finiteFieldLawOn (Λ n) (heightEvent B ξ)).toReal =
      ∑ S ∈ (Λ n).powerset, (pastProb Λ B S n).toReal * ratio B S ξ := by
  filter_upwards [hB] with n hn
  rw [finiteFieldLawOn_heightEvent hn ξ, ENNReal.toReal_sum fun S _ =>
    ENNReal.mul_ne_top (measure_ne_top _ _) (innerRatio_ne_top B S ξ)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [ENNReal.toReal_mul]

include hΛ in
/-- Convergence of the probability of prescribed heights along the exhaustion. -/
theorem tendsto_heightEvent_toReal {B : Finset Site2} (hB : B.Nonempty) (ξ : Site2 → ℕ) :
    Tendsto (fun n => (finiteFieldLawOn (Λ n) (heightEvent B ξ)).toReal) atTop
      (𝓝 (heightLimit B ξ)) := by
  set a := fun S => (pastWeight B S).toReal with ha
  have hsumA := hasSum_pastWeight_toReal hB
  have hsummable := summable_weight_ratio hB ξ
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpow : Tendsto (fun k => (centeredBox k).powerset) atTop atTop := by
    apply Filter.tendsto_atTop_finset_of_monotone
    · intro k k' hkk'
      exact Finset.powerset_mono.mpr (centeredBox_mono hkk')
    · intro S
      obtain ⟨k, hk⟩ := exists_subset_centeredBox S
      exact ⟨k, Finset.mem_powerset.mpr hk⟩
  have hpart := hsumA.comp hpow
  obtain ⟨k, hk1, hk2⟩ := (((tendsto_order.1 hpart).1 (1 - ε / 4) (by linarith)).and
    ((tendsto_order.1 (tendsto_tight_sum_toReal B)).2 (ε / 4) (by positivity))).exists
  simp only [Function.comp_apply] at hk1
  set P := (centeredBox k).powerset with hP
  set η := ε / (4 * (P.card + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hclose : ∀ᶠ n in atTop, ∀ S ∈ P, |(pastProb Λ B S n).toReal - a S| < η :=
    P.eventually_all.mpr fun S _ => by
      have := (tendsto_pastProb_toReal hΛ hB S)
      rw [Metric.tendsto_nhds] at this
      exact (this η hη).mono fun n hn => by rwa [Real.dist_eq] at hn
  have htightn := (tendsto_order.1 (tendsto_volume_tight_sum_toReal hΛ B k)).2 (ε / 4)
    (by linarith)
  filter_upwards [hclose, htightn, eventually_tight_bound hΛ B k, hΛ (centeredBox k),
    eventually_heightEvent_eq B ξ (hΛ B)] with n h1 h2 h3 hbox heq
  rw [heq, Real.dist_eq]
  have hsub : P ⊆ (Λ n).powerset := Finset.powerset_mono.mpr hbox
  rw [← Finset.sum_sdiff hsub]
  have htotal := sum_pastProb_volume (Λ := Λ) B n
  have hbsum := sum_pastProb_add (Λ := Λ) B n k
  rw [← Finset.sum_sdiff hsub] at htotal
  have htail : ∑ S ∈ (Λ n).powerset \ P, (pastProb Λ B S n).toReal =
      ((graph (Λ n)).treeLaw {t | ¬pastSites (Λ n) B t ⊆ centeredBox k}).toReal := by
    have h' : ∑ S ∈ (Λ n).powerset \ P, pastProb Λ B S n =
        (graph (Λ n)).treeLaw {t | ¬pastSites (Λ n) B t ⊆ centeredBox k} := by
      have := htotal.trans hbsum.symm
      exact (ENNReal.add_right_inj (ENNReal.sum_ne_top.mpr fun S _ =>
        pastProb_ne_top B S n)).mp (by rw [add_comm]; exact this)
    rw [← h', ENNReal.toReal_sum fun S _ => pastProb_ne_top B S n]
  have h3' : ((graph (Λ n)).treeLaw {t | ¬pastSites (Λ n) B t ⊆ centeredBox k}).toReal ≤
      ∑ b ∈ B, (volumeLaw Λ n (tightEvent b (centeredBox k))).toReal := by
    rw [← ENNReal.toReal_sum fun b _ => measure_ne_top _ _]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun b _ => measure_ne_top _ _) h3
  have hfar : 0 ≤ ∑ S ∈ (Λ n).powerset \ P, (pastProb Λ B S n).toReal * ratio B S ξ ∧
      ∑ S ∈ (Λ n).powerset \ P, (pastProb Λ B S n).toReal * ratio B S ξ ≤ ε / 4 := by
    constructor
    · exact Finset.sum_nonneg fun S _ => mul_nonneg ENNReal.toReal_nonneg (ratio_nonneg B S ξ)
    · calc ∑ S ∈ (Λ n).powerset \ P, (pastProb Λ B S n).toReal * ratio B S ξ
          ≤ ∑ S ∈ (Λ n).powerset \ P, (pastProb Λ B S n).toReal :=
            Finset.sum_le_sum fun S _ =>
              mul_le_of_le_one_right ENNReal.toReal_nonneg (ratio_le_one B S ξ)
        _ ≤ ε / 4 := by rw [htail]; linarith
  have hlim := hsummable.sum_add_tsum_compl (s := P)
  have hlimA := hsumA.summable.sum_add_tsum_compl (s := P)
  rw [hsumA.tsum_eq] at hlimA
  have htailL : 0 ≤ ∑' S : ↑((P : Set (Finset Site2))ᶜ), a S * ratio B S ξ ∧
      ∑' S : ↑((P : Set (Finset Site2))ᶜ), a S * ratio B S ξ ≤ ε / 4 := by
    constructor
    · exact tsum_nonneg fun S => mul_nonneg ENNReal.toReal_nonneg (ratio_nonneg B S ξ)
    · calc ∑' S : ↑((P : Set (Finset Site2))ᶜ), a S * ratio B S ξ
          ≤ ∑' S : ↑((P : Set (Finset Site2))ᶜ), a S :=
            Summable.tsum_le_tsum (fun S => mul_le_of_le_one_right ENNReal.toReal_nonneg
              (ratio_le_one B S ξ)) (hsummable.subtype _) (hsumA.summable.subtype _)
        _ ≤ ε / 4 := by
          have : ∑ S ∈ P, a S > 1 - ε / 4 := hk1
          linarith
  have hnear : |∑ S ∈ P, (pastProb Λ B S n).toReal * ratio B S ξ -
      ∑ S ∈ P, a S * ratio B S ξ| ≤ P.card * η := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ S ∈ P, ((pastProb Λ B S n).toReal * ratio B S ξ - a S * ratio B S ξ)|
        ≤ ∑ S ∈ P, |(pastProb Λ B S n).toReal * ratio B S ξ - a S * ratio B S ξ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _S ∈ P, η := by
          refine Finset.sum_le_sum fun S hS => ?_
          rw [← sub_mul, abs_mul, abs_of_nonneg (ratio_nonneg B S ξ)]
          calc |(pastProb Λ B S n).toReal - a S| * ratio B S ξ
              ≤ |(pastProb Λ B S n).toReal - a S| * 1 :=
                mul_le_mul_of_nonneg_left (ratio_le_one B S ξ) (abs_nonneg _)
            _ ≤ η := by rw [mul_one]; exact (h1 S hS).le
      _ = P.card * η := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcardη : (P.card : ℝ) * η ≤ ε / 4 := by
    rw [hηdef, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hε]
  have hL : heightLimit B ξ = ∑ S ∈ P, a S * ratio B S ξ +
      ∑' S : ↑((P : Set (Finset Site2))ᶜ), a S * ratio B S ξ := hlim.symm
  rw [hL]
  rw [abs_lt]
  constructor <;> nlinarith [abs_le.mp (le_of_lt_or_eq (Or.inl (lt_of_le_of_lt hnear
    (lt_of_le_of_lt hcardη (by linarith : ε / 4 < ε / 2)))) : |∑ S ∈ P,
      (pastProb Λ B S n).toReal * ratio B S ξ - ∑ S ∈ P, a S * ratio B S ξ| ≤ ε / 2),
    hfar.1, hfar.2, htailL.1, htailL.2]

end

end FiniteAvalanches.Sandpile.InfiniteVolume
