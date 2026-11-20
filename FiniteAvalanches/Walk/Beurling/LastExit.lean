/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/LastExit.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`Set.mem_ofPred_eq` replaced by `Set.mem_setOf_eq` (3 times); `measurableSet_setOfPred` replaced by
`measurableSet_setOf` (3 times); `Measurable.of_eval` replaced by `measurable_pi_lambda _` (once).
-/
import FiniteAvalanches.Walk.Beurling.GreenWalk

/-!
# The last-exit decomposition for the disk

For a finite set `B ⊆ C_r` and a start `z`, the probability that the simple random walk visits
`B` (time `0` allowed) before it leaves `C_r` is
`P_z(T⁰_B < τ_r) = ∑_{w ∈ B} G_r(z, w) P_w(τ_r < T_B)`.
This is formula (8) of G. F. Lawler and V. Limic, *The Beurling estimate for a class of random
walks*, Electron. J. Probab. 9 (2004); see also G. F. Lawler and V. Limic, *Random Walk: A
Modern Introduction*, Proposition 4.6.4.

The event `{T⁰_B < τ_r}` is split according to the last time `t < τ_r` at which the walk is in
`B` and the position `w` at that time. The walk leaves `C_r` almost surely, since the expected
number of visits to the finite set `C_r` is finite. Given that the walk stays in `C_r` up to
time `t` and is at `w` at time `t`, the shifted path from time `t` leaves `C_r` before a
positive-time visit to `B`, and the Markov property at the fixed time `t` factors the
probability of this event. Summing over `t` gives the Green function, by
`green_eq_tsum_visits`.

## Main statements

* `hitsBefore_eq_sum_green_mul`: `P_z(T⁰_B < τ_r) = ∑_{w ∈ B} G_r(z, w) P_w(τ_r < T_B)`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

private theorem mem_diskFinset_iff {r : ℝ} {z : Site 2} :
    z ∈ diskFinset r ↔ euclidNorm z < r := by
  rw [diskFinset, Finset.mem_filter, mem_ballFinset_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

private theorem green_nonneg (r : ℝ) (z w : Site 2) : 0 ≤ green r z w := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (diskFinset r)
  exact mul_nonneg (by norm_num)
    (Network.killedGreenReal_nonneg (Graph.Zd.latticeConnected 2) (diskFinset r) hq z w)

/-- The paths that visit `B` while still inside `C_r`. -/
private def hitPath (B : Set (Site 2)) (r : ℝ) : Set (ℕ → Site 2) :=
  {X | ∃ t, X t ∈ B ∧ ∀ s ≤ t, euclidNorm (X s) < r}

/-- The paths that leave `C_r` before a positive-time visit to `B`. -/
private def exitPath (r : ℝ) (B : Set (Site 2)) : Set (ℕ → Site 2) :=
  {X | ∃ t, r ≤ euclidNorm (X t) ∧ ∀ s, 1 ≤ s → s ≤ t → X s ∉ B}

/-- The paths that stay in `C_r` up to time `t` and are at `w` at time `t`. -/
private def stayPath (r : ℝ) (w : Site 2) (t : ℕ) : Set (ℕ → Site 2) :=
  {X | (∀ s ≤ t, euclidNorm (X s) < r) ∧ X t = w}

/-- The paths whose last visit to `B` before leaving `C_r` is at time `t`, at the site `w`. -/
private def lastPath (r : ℝ) (B : Set (Site 2)) (w : Site 2) (t : ℕ) : Set (ℕ → Site 2) :=
  stayPath r w t ∩ shiftPath t ⁻¹' exitPath r B

private theorem measurableSet_hitPath (B : Set (Site 2)) (r : ℝ) :
    MeasurableSet (hitPath B r) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    ((measurable_of_countable fun y : Site 2 => y ∈ B).comp (measurable_pi_apply t)).and <|
      Measurable.forall fun s =>
        (measurable_of_countable fun y : Site 2 => s ≤ t → euclidNorm y < r).comp
          (measurable_pi_apply s)

private theorem measurableSet_exitPath (r : ℝ) (B : Set (Site 2)) :
    MeasurableSet (exitPath r B) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    ((measurable_of_countable fun y : Site 2 => r ≤ euclidNorm y).comp
      (measurable_pi_apply t)).and <|
      Measurable.forall fun s =>
        (measurable_of_countable fun y : Site 2 => 1 ≤ s → s ≤ t → y ∉ B).comp
          (measurable_pi_apply s)

private theorem measurableSet_stayPath (r : ℝ) (w : Site 2) (t : ℕ) :
    MeasurableSet (stayPath r w t) :=
  measurableSet_setOf.2 <|
    (Measurable.forall fun s =>
      (measurable_of_countable fun y : Site 2 => s ≤ t → euclidNorm y < r).comp
        (measurable_pi_apply s)).and
    ((measurable_of_countable fun y : Site 2 => y = w).comp (measurable_pi_apply t))

private theorem measurableSet_lastPath (r : ℝ) (B : Set (Site 2)) (w : Site 2) (t : ℕ) :
    MeasurableSet (lastPath r B w t) :=
  (measurableSet_stayPath r w t).inter
    ((measurableSet_exitPath r B).preimage (measurable_shiftPath t))

private theorem measurable_walkPath (x : Site 2) :
    Measurable fun ω : ℕ → Dir 2 => walkPos x ω :=
  measurable_pi_lambda _ fun t => measurable_walkPos x t

/-- An event of the path of the walk has the same probability under `pathLaw` and under the
law `siteWalkLaw` of the path. -/
private theorem pathLaw_preimage (x : Site 2) {E : Set (ℕ → Site 2)} (hE : MeasurableSet E) :
    pathLaw 2 ((fun ω => walkPos x ω) ⁻¹' E) = siteWalkLaw 2 x E := by
  rw [← Measure.map_apply (measurable_walkPath x) hE]
  exact congrArg (· E) (pathLaw_map_sitePath 2 x)

/-- Summing the probabilities of `stayPath` over the time gives the Green function. -/
private theorem tsum_siteWalkLaw_stayPath (r : ℝ) (z w : Site 2) :
    ∑' t, siteWalkLaw 2 z (stayPath r w t) = ENNReal.ofReal (green r z w) := by
  have hset : ∀ t : ℕ,
      {ω : ℕ → Dir 2 | (∀ s ≤ t, walkPos z ω s ∈ diskFinset r) ∧ walkPos z ω t = w}
        = (fun ω => walkPos z ω) ⁻¹' stayPath r w t := fun t => by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, stayPath, mem_diskFinset_iff]
  have hm : ∀ t, MeasurableSet ((fun ω : ℕ → Dir 2 => walkPos z ω) ⁻¹' stayPath r w t) :=
    fun t => (measurableSet_stayPath r w t).preimage (measurable_walkPath z)
  rw [green_eq_tsum_visits]
  simp_rw [hset]
  rw [lintegral_tsum fun t => (measurable_one.indicator (hm t)).aemeasurable]
  refine tsum_congr fun t => ?_
  rw [lintegral_indicator_one (hm t), pathLaw_preimage z (measurableSet_stayPath r w t)]

/-- The walk leaves the disk `C_r` almost surely. -/
private theorem siteWalkLaw_stays (r : ℝ) (z : Site 2) :
    siteWalkLaw 2 z {X | ∀ u, euclidNorm (X u) < r} = 0 := by
  set a : ℕ → ENNReal := fun t => ∑ w ∈ diskFinset r, siteWalkLaw 2 z (stayPath r w t) with ha
  have hle : ∀ t, siteWalkLaw 2 z {X | ∀ u, euclidNorm (X u) < r} ≤ a t := fun t => by
    refine (measure_mono fun X hX => ?_).trans (measure_biUnion_finset_le _ _)
    exact Set.mem_biUnion (mem_diskFinset_iff.2 (hX t)) ⟨fun s _ => hX s, rfl⟩
  have hsum : ∑' t, a t ≠ ⊤ := by
    rw [ha, Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    refine ENNReal.sum_ne_top.2 fun w _ => ?_
    rw [tsum_siteWalkLaw_stayPath]
    exact ENNReal.ofReal_ne_top
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum) hle)
    (zero_le)

/-- **The Markov property at the time `t`.** -/
private theorem siteWalkLaw_lastPath (r : ℝ) (B : Set (Site 2)) (z w : Site 2) (t : ℕ) :
    siteWalkLaw 2 z (lastPath r B w t)
      = siteWalkLaw 2 z (stayPath r w t) * siteWalkLaw 2 w (exitPath r B) := by
  classical
  set F : (ℕ → Site 2) → ℝ := (exitPath r B).indicator 1 with hF
  set H : (ℕ → Site 2) → ℝ := (stayPath r w t).indicator 1 with hH
  have hFm : Measurable F := measurable_one.indicator (measurableSet_exitPath r B)
  have hb : ∀ (E : Set (ℕ → Site 2)) X, ‖E.indicator (1 : (ℕ → Site 2) → ℝ) X‖ ≤ 1 :=
    fun E X => by
      rw [Set.indicator_apply]
      split_ifs <;> simp
  have hdep : DependsUpTo t H := by
    intro X Y hXY
    have hiff : X ∈ stayPath r w t ↔ Y ∈ stayPath r w t := by
      simp only [stayPath, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨fun s hs => hXY s hs ▸ h₁ s hs, hXY t le_rfl ▸ h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨fun s hs => (hXY s hs).symm ▸ h₁ s hs, (hXY t le_rfl).symm ▸ h₂⟩
    simp only [hH, Set.indicator_apply, hiff, Pi.one_apply]
  have hmk := markov_fixed 2 t z F hFm (hb _) H (hb _) hdep
  have hL : (fun X => F (shiftPath t X) * H X) = (lastPath r B w t).indicator 1 := by
    funext X
    by_cases h₁ : X ∈ stayPath r w t <;> by_cases h₂ : shiftPath t X ∈ exitPath r B <;>
      simp [hF, hH, lastPath, h₁, h₂]
  have hR : (fun X => pathExpect 2 F (X t) * H X) = fun X => pathExpect 2 F w * H X := by
    funext X
    by_cases h : X ∈ stayPath r w t
    · rw [h.2]
    · simp [hH, h]
  rw [hL, hR, integral_indicator_one (measurableSet_lastPath r B w t), integral_const_mul,
    integral_indicator_one (measurableSet_stayPath r w t), pathExpect, hF,
    integral_indicator_one (measurableSet_exitPath r B)] at hmk
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)), ENNReal.toReal_mul]
  simp only [measureReal_def] at hmk
  rw [hmk, mul_comm]

/-- The last-exit decomposition of `hitPath` on the event that the walk leaves `C_r`. -/
private theorem hitPath_inter_subset {B : Set (Site 2)} {r : ℝ}
    (hB : ∀ w ∈ B, euclidNorm w < r) :
    hitPath B r ∩ {X | ∃ u, r ≤ euclidNorm (X u)} ⊆ ⋃ t, ⋃ w ∈ B, lastPath r B w t := by
  classical
  rintro X ⟨⟨t₀, ht₀B, ht₀⟩, hex⟩
  set τ := Nat.find hex
  have hτspec : r ≤ euclidNorm (X τ) := Nat.find_spec hex
  have hstay : ∀ s < τ, euclidNorm (X s) < r := fun s hs => lt_of_not_ge (Nat.find_min hex hs)
  have ht₀τ : t₀ < τ := lt_of_not_ge fun h => (ht₀ τ h).not_ge hτspec
  set σ := Nat.findGreatest (fun t => X t ∈ B) (τ - 1)
  have hσB : X σ ∈ B := Nat.findGreatest_spec (P := fun t => X t ∈ B) (by omega) ht₀B
  have hστ : σ < τ := lt_of_le_of_lt (Nat.findGreatest_le _) (by omega)
  refine Set.mem_iUnion.2 ⟨σ, Set.mem_biUnion hσB ⟨⟨fun s hs => hstay s (by omega), rfl⟩, ?_⟩⟩
  refine ⟨τ - σ, ?_, fun s hs₁ hs₂ hsB => ?_⟩
  · simp only [shiftPath]
    rwa [Nat.add_sub_cancel' hστ.le]
  · simp only [shiftPath] at hsB
    rcases Nat.lt_or_ge (σ + s) τ with h | h
    · exact Nat.findGreatest_is_greatest (P := fun t => X t ∈ B) (n := τ - 1)
        (by omega) (by omega) hsB
    · have : σ + s = τ := by omega
      rw [this] at hsB
      exact (hB _ hsB).not_ge hτspec

private theorem iUnion_lastPath_subset (B : Set (Site 2)) (r : ℝ) :
    ⋃ t, ⋃ w ∈ B, lastPath r B w t ⊆ hitPath B r := by
  intro X hX
  simp only [Set.mem_iUnion] at hX
  obtain ⟨t, w, hw, ⟨hs, hX⟩, -⟩ := hX
  exact ⟨t, hX ▸ hw, hs⟩

private theorem pairwise_disjoint_lastPath (B : Set (Site 2)) (r : ℝ) :
    Pairwise (Function.onFun Disjoint fun t => ⋃ w ∈ B, lastPath r B w t) := by
  have key : ∀ t t', t < t' → ∀ X, X ∈ ⋃ w ∈ B, lastPath r B w t →
      X ∉ ⋃ w ∈ B, lastPath r B w t' := by
    intro t t' htt' X hX hX'
    simp only [Set.mem_iUnion] at hX hX'
    obtain ⟨w, hw, -, ⟨u, hu, hnot⟩⟩ := hX
    obtain ⟨w', hw', ⟨hs', hX'⟩, -⟩ := hX'
    simp only [shiftPath] at hu hnot
    have hut : t' < t + u := lt_of_not_ge fun h => (hs' _ h).not_ge hu
    refine hnot (t' - t) (by omega) (by omega) ?_
    rw [Nat.add_sub_cancel' htt'.le, hX']
    exact hw'
  intro t t' htt'
  rcases Nat.lt_or_gt_of_ne htt' with h | h
  · exact Set.disjoint_left.2 (key t t' h)
  · exact Set.disjoint_right.2 (key t' t h)

/-- **Lawler-Limic (8).** For a finite set `B ⊆ C_r`, the probability that the walk started at
`z` visits `B` before it leaves `C_r` is `∑_{w ∈ B} G_r(z, w) P_w(τ_r < T_B)`. -/
theorem hitsBefore_eq_sum_green_mul (r : ℝ) (B' : Finset (Site 2))
    (hB' : ∀ w ∈ B', euclidNorm w < r) (z : Site 2) :
    prob (hitsBefore B' r z) = ∑ w ∈ B', green r z w * prob (exitsBefore r B' w) := by
  classical
  set B : Set (Site 2) := (B' : Set (Site 2)) with hBdef
  have hB : ∀ w ∈ B, euclidNorm w < r := fun w hw => hB' w hw
  have hU : siteWalkLaw 2 z (hitPath B r) = siteWalkLaw 2 z (⋃ t, ⋃ w ∈ B, lastPath r B w t) := by
    have hnull : siteWalkLaw 2 z {X : ℕ → Site 2 | ∃ u, r ≤ euclidNorm (X u)}ᶜ = 0 := by
      have : {X : ℕ → Site 2 | ∃ u, r ≤ euclidNorm (X u)}ᶜ = {X | ∀ u, euclidNorm (X u) < r} := by
        ext X
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_le]
      rw [this, siteWalkLaw_stays]
    refine le_antisymm ?_ (measure_mono (iUnion_lastPath_subset B r))
    rw [← measure_inter_conull hnull]
    exact measure_mono (hitPath_inter_subset hB)
  have hkey : pathLaw 2 (hitsBefore B r z)
      = ∑ w ∈ B', ENNReal.ofReal (green r z w) * pathLaw 2 (exitsBefore r B w) := by
    have h₁ : hitsBefore B r z = (fun ω => walkPos z ω) ⁻¹' hitPath B r := rfl
    have h₂ : ∀ w, exitsBefore r B w = (fun ω => walkPos w ω) ⁻¹' exitPath r B := fun _ => rfl
    simp_rw [h₂]
    rw [h₁, pathLaw_preimage z (measurableSet_hitPath B r), hU,
      measure_iUnion (pairwise_disjoint_lastPath B r) fun t =>
        Finset.measurableSet_biUnion _ fun w _ => measurableSet_lastPath r B w t]
    have hinner : ∀ t, siteWalkLaw 2 z (⋃ w ∈ B, lastPath r B w t)
        = ∑ w ∈ B', siteWalkLaw 2 z (stayPath r w t) * siteWalkLaw 2 w (exitPath r B) := by
      intro t
      have hBU : (⋃ w ∈ B, lastPath r B w t) = ⋃ w ∈ B', lastPath r B w t := by
        simp only [hBdef, Finset.mem_coe]
      rw [hBU, measure_biUnion_finset (fun w _ w' _ hww' => Set.disjoint_left.2
          fun X hX hX' => hww' (hX.1.2.symm.trans hX'.1.2))
          fun w _ => measurableSet_lastPath r B w t]
      exact Finset.sum_congr rfl fun w _ => siteWalkLaw_lastPath r B z w t
    simp_rw [hinner]
    rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ENNReal.tsum_mul_right, tsum_siteWalkLaw_stayPath,
      pathLaw_preimage w (measurableSet_exitPath r B)]
  rw [prob, hkey, ENNReal.toReal_sum fun w _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (green_nonneg r z w), prob]

end FiniteAvalanches.Walk.Beurling
