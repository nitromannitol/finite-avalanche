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

end

end FiniteAvalanches.Sandpile.InfiniteVolume
