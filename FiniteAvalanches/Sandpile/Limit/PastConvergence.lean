import FiniteAvalanches.Sandpile.Limit.GammaPasts
import FiniteAvalanches.Trees.Lattice.PastLimit
import FiniteAvalanches.Sandpile.Law.Properties

/-! Along any exhaustion of `ℤ²`, the probability that the union of the pasts of a nonempty
finite set `B` in the wired uniform spanning tree of the volume is `S` converges to the
probability of the limiting past event under the wired uniform spanning tree of `ℤ²`.

The upper bound comes from the local past events, which converge weakly; the lower bound
from the dual tightness bound and the fact that the limiting probabilities sum to one. -/

set_option autoImplicit false

namespace FiniteAvalanches.Sandpile.InfiniteVolume

open LatticeProb MeasureTheory Filter Topology FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.Lattice.SiteRoots FiniteAvalanches.Sandpile.GammaGraph
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal

noncomputable section

variable {Λ : ℕ → Finset Site2} (hΛ : IsExhaustion Λ)

/-- The lattice edge law of the wired uniform spanning tree of the `n`-th volume. -/
abbrev volumeLaw (Λ : ℕ → Finset Site2) (n : ℕ) : Measure EdgeField :=
  forestLaw ((Λ n : Finset Site2) : Set Site2) (GammaGraph.radius (Λ n))

/-- The law of the union of the pasts of `B` in the `n`-th volume. -/
abbrev pastProb (Λ : ℕ → Finset Site2) (B S : Finset Site2) (n : ℕ) : ℝ≥0∞ :=
  (graph (Λ n)).treeLaw {t | pastSites (Λ n) B t = S}

include hΛ in
theorem volumeLaw_tendsto_clopen {E : Set EdgeField} (hE : IsClopen E) :
    Tendsto (fun n => volumeLaw Λ n E) atTop (𝓝 (ustMeasure E)) := by
  have hweak := forestProbability_tendsto (fun n => ((Λ n : Finset Site2) : Set Site2))
    (fun n => GammaGraph.radius (Λ n)) (fun n x hx => in_radius ⟨x, hx⟩) (fun m => by
      filter_upwards [hΛ (centeredBox m)] with n hn
      intro x hx
      apply hn
      rw [mem_centeredBox]
      exact fun i => hx i)
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak
    (by rw [hE.frontier_eq]; exact measure_empty)

include hΛ in
theorem eventually_nbr_subset (B : Finset Site2) :
    ∀ᶠ n in atTop, B ⊆ Λ n ∧ ∀ b ∈ B, ∀ w, (lattice 2).Adj b w → w ∈ Λ n := by
  filter_upwards [hΛ B, hΛ (centeredBox (nbrBox B))] with n h1 h2
  exact ⟨h1, fun b hb w hw => h2 (nbr_mem_nbrBox hb hw)⟩

include hΛ in
theorem eventually_pastProb_le (B S : Finset Site2) {m : ℕ} (hm : nbrBox B ≤ m) :
    ∀ᶠ n in atTop, pastProb Λ B S n ≤ volumeLaw Λ n (pastEvent B S (centeredBox m)) := by
  filter_upwards [hΛ B, hΛ (centeredBox m)] with n hB hW
  exact treeLaw_pastSites_le (Λ n) hB hW fun b hb w hw =>
    centeredBox_mono hm (nbr_mem_nbrBox hb hw)

theorem nbr_mem_centeredBox_succ {k : ℕ} {x z : Site2} (h0 : |x 0| ≤ k) (h1 : |x 1| ≤ k)
    (hxz : (lattice 2).Adj x z) : z ∈ centeredBox (k + 1) := by
  rw [mem_centeredBox]
  have hk : ∀ i, |x i| ≤ k := fun i => by fin_cases i <;> assumption
  obtain ⟨i, rfl | rfl⟩ := hxz
  · intro j
    have := abs_le.mp (hk j)
    by_cases hij : j = i
    · subst hij
      simp only [Pi.add_apply, unit, Pi.single_eq_same]
      push_cast
      constructor <;> omega
    · simp only [Pi.add_apply, unit, Pi.single_apply, hij, if_false, add_zero]
      push_cast
      constructor <;> omega
  · intro j
    have := abs_le.mp (hk j)
    by_cases hij : j = i
    · subst hij
      simp only [Pi.add_apply, unit, Pi.single_eq_same] at this
      push_cast
      constructor <;> omega
    · simp only [Pi.add_apply, unit, Pi.single_apply, hij, if_false, add_zero] at this
      push_cast
      constructor <;> omega

include hΛ in
theorem eventually_tight_bound (B : Finset Site2) (k : ℕ) :
    ∀ᶠ n in atTop, (graph (Λ n)).treeLaw {t | ¬pastSites (Λ n) B t ⊆ centeredBox k} ≤
      ∑ b ∈ B, volumeLaw Λ n (tightEvent b (centeredBox k)) := by
  filter_upwards [eventually_nbr_subset hΛ B, hΛ (centeredBox (k + 1))] with n hn hbox
  exact treeLaw_pastSites_not_subset_le (Λ n) hn.1 hn.2 k fun x h0 h1 z hz =>
    hbox (nbr_mem_centeredBox_succ h0 h1 hz)

/-- The past laws over the subsets of a box and the tail outside it add up to one. -/
theorem sum_pastProb_add (B : Finset Site2) (n k : ℕ) :
    ∑ S ∈ (centeredBox k).powerset, pastProb Λ B S n +
      (graph (Λ n)).treeLaw {t | ¬pastSites (Λ n) B t ⊆ centeredBox k} = 1 := by
  have hdisj : (⋃ S ∈ (centeredBox k).powerset, {t : (graph (Λ n)).SpanningTree |
      pastSites (Λ n) B t = S}) = {t | pastSites (Λ n) B t ⊆ centeredBox k} := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_powerset, exists_prop]
    exact ⟨fun ⟨S, hS, he⟩ => he ▸ hS, fun h => ⟨_, h, rfl⟩⟩
  have hsum : ∑ S ∈ (centeredBox k).powerset, pastProb Λ B S n =
      (graph (Λ n)).treeLaw {t | pastSites (Λ n) B t ⊆ centeredBox k} := by
    rw [← hdisj, measure_biUnion_finset]
    · intro S _ S' _ hne
      exact Set.disjoint_left.mpr fun t h1 h2 => hne (h1.symm.trans h2)
    · exact fun _ _ => measurableSet_setOf.mpr (measurable_of_countable _)
  rw [hsum, ← measure_union]
  · have hu : {t : (graph (Λ n)).SpanningTree | pastSites (Λ n) B t ⊆ centeredBox k} ∪
        {t | ¬pastSites (Λ n) B t ⊆ centeredBox k} = Set.univ := by
      ext t
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact em _
    rw [hu]
    exact measure_univ
  · exact Set.disjoint_left.mpr fun t h1 h2 => h2 h1
  · exact measurableSet_setOf.mpr (measurable_of_countable _)

/-- The limiting probability of the past event of `B` with set `S`. -/
abbrev pastWeight (B S : Finset Site2) : ℝ≥0∞ := ustMeasure (pastLimitEvent B S)

include hΛ in
/-- Upper bound: eventually below any number above the limiting probability. -/
theorem eventually_pastProb_lt (B S : Finset Site2) {c : ℝ≥0∞} (hc : pastWeight B S < c) :
    ∀ᶠ n in atTop, pastProb Λ B S n < c := by
  have hlim := tendsto_pastEvent ustMeasure B S
  obtain ⟨m, hm⟩ := (((tendsto_order.1 hlim).2 c hc).and
    (eventually_ge_atTop (nbrBox B))).exists
  have hclop := volumeLaw_tendsto_clopen hΛ (isClopen_pastEvent B S (centeredBox m))
  filter_upwards [eventually_pastProb_le hΛ B S hm.2, (tendsto_order.1 hclop).2 c hm.1]
    with n h1 h2
  exact lt_of_le_of_lt h1 h2

theorem pastWeight_ne_top (B S : Finset Site2) : pastWeight B S ≠ ⊤ := measure_ne_top _ _

theorem pastProb_ne_top (B S : Finset Site2) (n : ℕ) : pastProb Λ B S n ≠ ⊤ :=
  measure_ne_top _ _

include hΛ in
theorem eventually_pastProb_toReal_lt (B S : Finset Site2) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, (pastProb Λ B S n).toReal < (pastWeight B S).toReal + η := by
  have hc : pastWeight B S < ENNReal.ofReal ((pastWeight B S).toReal + η) := by
    rw [← ENNReal.ofReal_toReal (pastWeight_ne_top B S)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]; linarith)
  filter_upwards [eventually_pastProb_lt hΛ B S hc] with n hn
  have := (ENNReal.toReal_lt_toReal (pastProb_ne_top B S n) ENNReal.ofReal_ne_top).mpr hn
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

theorem hasSum_pastWeight_toReal {B : Finset Site2} (hB : B.Nonempty) :
    HasSum (fun S => (pastWeight B S).toReal) 1 := by
  have h := hasSum_pastLimitEvent hB
  have hs := ENNReal.hasSum_toReal (f := fun S => pastWeight B S) (by
    rw [h.tsum_eq]
    exact ENNReal.one_ne_top)
  rw [← ENNReal.tsum_toReal_eq (fun S => pastWeight_ne_top B S), h.tsum_eq,
    ENNReal.toReal_one] at hs
  exact hs

theorem tendsto_tight_sum_toReal (B : Finset Site2) :
    Tendsto (fun k => ∑ b ∈ B, (ustMeasure (tightEvent b (centeredBox k))).toReal) atTop
      (𝓝 0) := by
  have h : Tendsto (fun k => ∑ b ∈ B, (ustMeasure (tightEvent b (centeredBox k))).toReal) atTop
      (𝓝 (∑ _b ∈ B, (0 : ℝ))) :=
    tendsto_finsetSum _ fun b _ => by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_tightEvent b)
      rw [ENNReal.toReal_zero] at h
      exact h
  simpa using h

include hΛ in
theorem tendsto_volume_tight_sum_toReal (B : Finset Site2) (k : ℕ) :
    Tendsto (fun n => ∑ b ∈ B, (volumeLaw Λ n (tightEvent b (centeredBox k))).toReal) atTop
      (𝓝 (∑ b ∈ B, (ustMeasure (tightEvent b (centeredBox k))).toReal)) :=
  tendsto_finsetSum _ fun b _ => (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (volumeLaw_tendsto_clopen hΛ (isClopen_tightEvent b _))

include hΛ in
/-- The probability that the past of `B` is `S` converges along the exhaustion. -/
theorem tendsto_pastProb_toReal {B : Finset Site2} (hB : B.Nonempty) (S : Finset Site2) :
    Tendsto (fun n => (pastProb Λ B S n).toReal) atTop (𝓝 (pastWeight B S).toReal) := by
  set a := fun S' => (pastWeight B S').toReal with ha
  have hsumA := hasSum_pastWeight_toReal hB
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · set δ := a S - c with hδ
    have hδpos : 0 < δ := by simp only [hδ]; linarith
    obtain ⟨k, hk⟩ := (((tendsto_order.1 (tendsto_tight_sum_toReal B)).2 (δ / 4)
      (by positivity)).and (eventually_subset_centeredBox S)).exists
    set F := (centeredBox k).powerset.erase S with hF
    have hSmem : S ∈ (centeredBox k).powerset := Finset.mem_powerset.mpr hk.2
    set η := δ / (4 * (F.card + 1)) with hηdef
    have hη : 0 < η := by positivity
    have hFsum : a S + ∑ S' ∈ F, a S' ≤ 1 := by
      have := sum_le_hasSum (insert S F) (fun _ _ => ENNReal.toReal_nonneg) hsumA
      rwa [Finset.sum_insert (Finset.notMem_erase S _)] at this
    have hall : ∀ᶠ n in atTop, ∀ S' ∈ F, (pastProb Λ B S' n).toReal < a S' + η :=
      F.eventually_all.mpr fun S' _ => eventually_pastProb_toReal_lt hΛ B S' hη
    have htightn := (tendsto_order.1 (tendsto_volume_tight_sum_toReal hΛ B k)).2
      (∑ b ∈ B, (ustMeasure (tightEvent b (centeredBox k))).toReal + δ / 4)
      (by linarith)
    filter_upwards [hall, htightn, eventually_tight_bound hΛ B k] with n h1 h2 h3
    have htot := sum_pastProb_add (Λ := Λ) B n k
    rw [← Finset.add_sum_erase _ _ hSmem] at htot
    have htot' := congrArg ENNReal.toReal htot
    rw [ENNReal.toReal_add (by
        exact ENNReal.add_ne_top.mpr ⟨pastProb_ne_top B S n,
          ENNReal.sum_ne_top.mpr fun S' _ => pastProb_ne_top B S' n⟩) (measure_ne_top _ _),
      ENNReal.toReal_add (pastProb_ne_top B S n)
        (ENNReal.sum_ne_top.mpr fun S' _ => pastProb_ne_top B S' n),
      ENNReal.toReal_sum fun S' _ => pastProb_ne_top B S' n, ENNReal.toReal_one] at htot'
    have h3' : ((graph (Λ n)).treeLaw {t | ¬pastSites (Λ n) B t ⊆ centeredBox k}).toReal ≤
        ∑ b ∈ B, (volumeLaw Λ n (tightEvent b (centeredBox k))).toReal := by
      rw [← ENNReal.toReal_sum fun b _ => measure_ne_top _ _]
      exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun b _ => measure_ne_top _ _) h3
    have hFlt : ∑ S' ∈ F, (pastProb Λ B S' n).toReal ≤ ∑ S' ∈ F, a S' + F.card * η := by
      have := Finset.sum_le_sum fun S' hS' => (h1 S' hS').le
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at this
      exact this
    have hcardη : (F.card : ℝ) * η ≤ δ / 4 := by
      rw [hηdef, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hδpos]
    have hk1 := hk.1
    linarith
  · exact (eventually_pastProb_toReal_lt hΛ B S (by linarith : 0 < c - a S)).mono
      fun n hn => by linarith

end

end FiniteAvalanches.Sandpile.InfiniteVolume
