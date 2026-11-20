/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/HalfLine.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`measurableSet_setOfPred` replaced by `measurableSet_setOf` (2 times); `Measurable.of_eval` replaced
by `measurable_pi_lambda _` (once).
-/
import FiniteAvalanches.Walk.Beurling.HitDense
import FiniteAvalanches.Walk.Beurling.HitPoint

/-!
# Returning to the start before hitting a half-line

For the simple random walk on `ℤ²` started at `(-n, 0)`, the probability that the first
positive-time visit to `{(-n, 0)} ∪ {(j, 0) : j ≥ 0}` is a return to the start is at most
`1 - c / log n`. This is Lemma 11 (a) of G. F. Lawler and V. Limic, *The Beurling estimate for a
class of random walks*, Electron. J. Probab. 9 (2004).

After a translation the walk starts at the origin and the half-line is `{(j, 0) : j ≥ n}`. The
walk leaves the disk `C_n` before it returns to the origin with probability `1 / G_n(0, 0)`, by
formula (8), and this is at least `c / log n` by Lemma 3. The site `w` where the walk first
leaves `C_n` satisfies `n ≤ |w| < n + 1`. From `w`, the walk visits the segment `[n, 2n)` of the
real axis before it leaves `C_{4n}` with probability at least a constant, by Lemma 7 for the
dense set of nonnegative integers on the real axis, and it visits the origin before it leaves
`C_{4n}` with probability at most `c / log n`, by Lemma 8. The Markov property at the first exit
time from `C_n` combines the two estimates.

## Main statements

* `return_before_halfLine`: Lawler-Limic (2004), Lemma 11 (a).
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

/-- The paths that visit `B` while still inside `C_r`. -/
private def visitPath (B : Set (Site 2)) (r : ℝ) : Set (ℕ → Site 2) :=
  {X | ∃ t, X t ∈ B ∧ ∀ s ≤ t, euclidNorm (X s) < r}

/-- The paths that first leave `C_r` at the time `t`, at a site `w` with `r ≤ |w| < r + 1`, with
no positive-time visit to the origin up to time `t`. -/
private def firstExitPath (r : ℝ) (w : Site 2) (t : ℕ) : Set (ℕ → Site 2) :=
  {X | r ≤ euclidNorm w ∧ euclidNorm w < r + 1 ∧ X t = w ∧ (∀ s < t, euclidNorm (X s) < r) ∧
    ∀ s, 1 ≤ s → s ≤ t → X s ≠ 0}

/-- The paths that visit the part of the nonnegative real axis between radii `m / 4` and `m / 2`
before they leave `C_m`, and that do not visit the origin before they leave `C_m`. -/
private def segmentPath (m : ℕ) : Set (ℕ → Site 2) :=
  visitPath (shellPart (axisSet {j | 0 ≤ j}) ((m : ℝ) / 4) ((m : ℝ) / 2)) m \ visitPath {0} m

private theorem measurableSet_visitPath (B : Set (Site 2)) (r : ℝ) :
    MeasurableSet (visitPath B r) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    ((measurable_of_countable fun y : Site 2 => y ∈ B).comp (measurable_pi_apply t)).and <|
      Measurable.forall fun s =>
        (measurable_of_countable fun y : Site 2 => s ≤ t → euclidNorm y < r).comp
          (measurable_pi_apply s)

private theorem measurableSet_segmentPath (m : ℕ) : MeasurableSet (segmentPath m) :=
  (measurableSet_visitPath _ _).diff (measurableSet_visitPath _ _)

private theorem measurableSet_firstExitPath (r : ℝ) (w : Site 2) (t : ℕ) :
    MeasurableSet (firstExitPath r w t) :=
  measurableSet_setOf.2 <| measurable_const.and <| measurable_const.and <|
    ((measurable_of_countable fun y : Site 2 => y = w).comp (measurable_pi_apply t)).and <|
      (Measurable.forall fun s =>
        (measurable_of_countable fun y : Site 2 => s < t → euclidNorm y < r).comp
          (measurable_pi_apply s)).and <|
      Measurable.forall fun s =>
        (measurable_of_countable fun y : Site 2 => 1 ≤ s → s ≤ t → y ≠ 0).comp
          (measurable_pi_apply s)

private theorem measurable_walkPath (x : Site 2) :
    Measurable fun ω : ℕ → Dir 2 => walkPos x ω :=
  measurable_pi_lambda _ fun t => measurable_walkPos x t

/-- An event of the path of the walk has the same probability under `pathLaw` and under the
law `siteWalkLaw` of the path. -/
private theorem pathLaw_preimage (x : Site 2) {E : Set (ℕ → Site 2)} (hE : MeasurableSet E) :
    pathLaw 2 ((fun ω => walkPos x ω) ⁻¹' E) = siteWalkLaw 2 x E := by
  rw [← Measure.map_apply (measurable_walkPath x) hE]
  exact congrArg (· E) (pathLaw_map_sitePath 2 x)

/-- **The Markov property at the time `t`** for an event settled by the positions up to time `t`
on which the position at time `t` is `w`. -/
private theorem siteWalkLaw_inter_shift {P G : Set (ℕ → Site 2)} (z w : Site 2) (t : ℕ)
    (hPm : MeasurableSet P) (hGm : MeasurableSet G)
    (hP : ∀ X Y : ℕ → Site 2, (∀ k ≤ t, X k = Y k) → X ∈ P → Y ∈ P)
    (hPw : ∀ X ∈ P, X t = w) :
    siteWalkLaw 2 z (P ∩ shiftPath t ⁻¹' G) = siteWalkLaw 2 z P * siteWalkLaw 2 w G := by
  classical
  set F : (ℕ → Site 2) → ℝ := G.indicator 1 with hF
  set H : (ℕ → Site 2) → ℝ := P.indicator 1 with hH
  have hFm : Measurable F := measurable_one.indicator hGm
  have hb : ∀ (E : Set (ℕ → Site 2)) X, ‖E.indicator (1 : (ℕ → Site 2) → ℝ) X‖ ≤ 1 :=
    fun E X => by
      rw [Set.indicator_apply]
      split_ifs <;> simp
  have hdep : DependsUpTo t H := by
    intro X Y hXY
    have hiff : X ∈ P ↔ Y ∈ P := ⟨hP X Y hXY, hP Y X fun k hk => (hXY k hk).symm⟩
    simp only [hH, Set.indicator_apply, hiff, Pi.one_apply]
  have hmk := markov_fixed 2 t z F hFm (hb _) H (hb _) hdep
  have hL : (fun X => F (shiftPath t X) * H X) = (P ∩ shiftPath t ⁻¹' G).indicator 1 := by
    funext X
    by_cases h₁ : X ∈ P <;> by_cases h₂ : shiftPath t X ∈ G <;> simp [hF, hH, h₁, h₂]
  have hR : (fun X => pathExpect 2 F (X t) * H X) = fun X => pathExpect 2 F w * H X := by
    funext X
    by_cases h : X ∈ P
    · rw [hPw X h]
    · simp [hH, h]
  rw [hL, hR, integral_indicator_one (hPm.inter (hGm.preimage (measurable_shiftPath t))),
    integral_const_mul, integral_indicator_one hPm, pathExpect, hF,
    integral_indicator_one hGm] at hmk
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)), ENNReal.toReal_mul]
  simp only [measureReal_def] at hmk
  rw [hmk, mul_comm]

private theorem firstExitPath_congr {r : ℝ} {w : Site 2} {t : ℕ} (X Y : ℕ → Site 2)
    (hXY : ∀ k ≤ t, X k = Y k) (hX : X ∈ firstExitPath r w t) : Y ∈ firstExitPath r w t := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hX
  refine ⟨h₁, h₂, ?_, fun s hs => ?_, fun s hs₁ hs₂ => ?_⟩
  · rw [← hXY t le_rfl]
    exact h₃
  · rw [← hXY s hs.le]
    exact h₄ s hs
  · rw [← hXY s hs₂]
    exact h₅ s hs₁ hs₂

private theorem pairwise_disjoint_firstExitPath (r : ℝ) :
    Pairwise (Function.onFun Disjoint fun p : ℕ × Site 2 => firstExitPath r p.2 p.1) := by
  rintro ⟨t, w⟩ ⟨t', w'⟩ hne
  refine Set.disjoint_left.2 fun X hX hX' => hne ?_
  obtain ⟨hw, -, hXt, hlt, -⟩ := hX
  obtain ⟨hw', -, hXt', hlt', -⟩ := hX'
  dsimp only at hw hXt hlt hw' hXt' hlt'
  have htt : t = t' := by
    rcases lt_trichotomy t t' with h | h | h
    · refine absurd (hlt' t h) (not_lt.2 ?_)
      rw [hXt]
      exact hw
    · exact h
    · refine absurd (hlt t' h) (not_lt.2 ?_)
      rw [hXt']
      exact hw'
  subst htt
  rw [← hXt, ← hXt']

private theorem walkPos_eq_add (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos x ω t = x + walkPos 0 ω t := by
  simp [walkPos]

private theorem euclidNorm_walkPos_zero (ω : ℕ → Dir 2) : euclidNorm (walkPos 0 ω 0) = 0 := by
  simp [walkPos, euclidNorm]

private theorem euclidNorm_of_snd_eq_zero {z : Site 2} (hz : z 1 = 0) :
    euclidNorm z = |((z 0 : ℤ) : ℝ)| := by
  rw [euclidNorm, Fin.sum_univ_two, hz]
  simp [Real.sqrt_sq_eq_abs]

private theorem isDense_axisSet_nonneg : IsDense (axisSet {j | 0 ≤ j}) := by
  intro j
  refine ⟨axisPt j, ⟨by simp [axisPt], by simp [axisPt]⟩, ?_⟩
  have h : euclidNorm (axisPt j) = j := by
    rw [euclidNorm_of_snd_eq_zero (by simp [axisPt])]
    simp [axisPt]
  rw [h]
  exact ⟨le_rfl, by linarith⟩

/-- **The escape probability of the origin.** `G_r(0, 0) P_0(τ_r < T_0) = 1`. -/
private theorem green_mul_prob_exitsBefore {r : ℝ} (hr : 0 < r) :
    green r 0 0 * prob (exitsBefore r {0} 0) = 1 := by
  have h := hitsBefore_eq_sum_green_mul r {0} (fun w hw => by
    rw [Finset.mem_singleton.1 hw]
    simpa [euclidNorm] using hr) 0
  rw [Finset.sum_singleton, Finset.coe_singleton] at h
  rw [← h]
  have hU : hitsBefore {0} r 0 = Set.univ := by
    ext ω
    simp only [Set.mem_univ, iff_true]
    refine ⟨0, by simp [walkPos], fun s hs => ?_⟩
    have : s = 0 := by omega
    subst s
    rw [euclidNorm_walkPos_zero]
    exact hr
  rw [hU, prob, measure_univ, ENNReal.toReal_one]

/-- Every path that leaves `C_n` before it returns to the origin has a first exit time. -/
private theorem exitsBefore_subset {n : ℕ} (hn : 0 < n) :
    exitsBefore n {0} 0 ⊆
      (fun ω => walkPos 0 ω) ⁻¹' ⋃ p : ℕ × Site 2, firstExitPath n p.2 p.1 := by
  classical
  rintro ω ⟨t, ht, hne⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hex : ∃ s, (n : ℝ) ≤ euclidNorm (walkPos 0 ω s) := ⟨t, ht⟩
  obtain ⟨s, hspec, hmin⟩ : ∃ s, (n : ℝ) ≤ euclidNorm (walkPos 0 ω s) ∧
      ∀ k < s, euclidNorm (walkPos 0 ω k) < n :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => lt_of_not_ge (Nat.find_min hex hk)⟩
  have hst : s ≤ t := le_of_not_gt fun h => (hmin t h).not_ge ht
  have hs1 : 1 ≤ s := by
    by_contra h
    have h0 : s = 0 := by omega
    rw [h0, euclidNorm_walkPos_zero] at hspec
    linarith
  simp only [Set.mem_preimage, Set.mem_iUnion]
  refine ⟨(s, walkPos 0 ω s), hspec, ?_, rfl, hmin, fun k hk₁ hks => hne k hk₁ (hks.trans hst)⟩
  have hstep := euclidNorm_walkPos_succ_le 0 ω (s - 1)
  rw [Nat.sub_add_cancel hs1] at hstep
  linarith [hmin (s - 1) (by omega)]

/-- A path that first leaves `C_n` at `w` without returning to the origin and then visits the
segment `[n, 2n)` of the real axis before it visits the origin does not return to the origin
before it visits the half-line `{(j, 0) : j ≥ n}`. -/
private theorem not_mem_entersAt {n : ℕ} (hn : 0 < n) {ω : ℕ → Dir 2} {t : ℕ} {w : Site 2}
    (hX : walkPos 0 ω ∈ firstExitPath n w t)
    (hY : shiftPath t (walkPos 0 ω) ∈ segmentPath (4 * n)) :
    ω ∉ entersAt ({axisPt (-n)} ∪ axisSet {j | 0 ≤ j}) (axisPt (-n)) (axisPt (-n)) := by
  rintro ⟨t₀, ht₀, hx, hB⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hrw, -, hXt, -, hne⟩ := hX
  obtain ⟨⟨u, hu, hustay⟩, hno⟩ := hY
  simp only [shiftPath] at hu hustay hno
  rw [walkPos_eq_add] at hx
  have hx0 : walkPos 0 ω t₀ = 0 := by simpa using hx
  have ht1 : 1 ≤ t := by
    by_contra h
    have h0 : t = 0 := by omega
    rw [h0] at hXt
    rw [← hXt, euclidNorm_walkPos_zero] at hrw
    linarith
  rcases le_or_gt t₀ t with h₁ | h₁
  · exact hne t₀ ht₀ h₁ hx0
  rcases le_or_gt t₀ (t + u) with h₂ | h₂
  · refine hno ⟨t₀ - t, ?_, fun s hs => hustay s (by omega)⟩
    show walkPos 0 ω (t + (t₀ - t)) ∈ ({0} : Set (Site 2))
    rw [Nat.add_sub_cancel' h₁.le]
    exact hx0
  · refine hB (t + u) (by omega) h₂ (Set.mem_union_right _ ?_)
    obtain ⟨⟨hz1, hz0⟩, hlow, -⟩ := hu
    have hz0' : (0 : ℤ) ≤ walkPos 0 ω (t + u) 0 := hz0
    rw [euclidNorm_of_snd_eq_zero hz1, abs_of_nonneg (by exact_mod_cast hz0')] at hlow
    have h4 : ((4 * n : ℕ) : ℝ) / 4 = n := by
      push_cast
      ring
    rw [h4] at hlow
    have hle : (n : ℤ) ≤ walkPos 0 ω (t + u) 0 := by exact_mod_cast hlow
    rw [walkPos_eq_add]
    refine ⟨?_, ?_⟩
    · simp [axisPt, hz1]
    · show 0 ≤ (axisPt (-n) + walkPos 0 ω (t + u)) 0
      simp only [axisPt, Pi.add_apply, Matrix.cons_val_zero]
      omega

/-- **Lawler-Limic (2004), Lemma 11 (a).** The walk started at `(-n, 0)` returns to its start
before it visits the half-line `{(j, 0) : j ≥ 0}` with probability at most `1 - c / log n`. -/
theorem return_before_halfLine : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    prob (entersAt ({axisPt (-n)} ∪ axisSet {j | 0 ≤ j}) (axisPt (-n)) (axisPt (-n))) ≤
      1 - c / Real.log n := by
  classical
  obtain ⟨c₇, hc₇, N₇, h₇⟩ := hit_shellPart_lower
  obtain ⟨c₁, c₂, hc₁, hc₂, N₈, h₈⟩ := hit_origin_annulus
  obtain ⟨C, hC⟩ := green_asymptotics
  set M : ℝ := 2 * c₂ / c₇ + |C| + 1 with hM
  refine ⟨c₇ * Real.pi / 8, by positivity, N₇ + N₈ + 2 + ⌈Real.exp M⌉₊, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hcc : 0 ≤ 2 * c₂ / c₇ := by positivity
  have hlogM : M ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnR]
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp M⌉₊ ≤ n by omega))
  have hM1 : 1 ≤ M := by
    have : 0 ≤ 2 * c₂ / c₇ := by positivity
    have := abs_nonneg C
    linarith
  have hlog : 0 < Real.log n := by linarith
  have h4n : ((4 * n : ℕ) : ℝ) = 4 * n := by push_cast; ring
  have hlog4 : Real.log n ≤ Real.log ((4 * n : ℕ) : ℝ) := by
    rw [h4n]
    exact Real.log_le_log hnR (by linarith)
  have hδ : c₂ / Real.log ((4 * n : ℕ) : ℝ) ≤ c₇ / 2 := by
    have hL : 2 * c₂ / c₇ ≤ Real.log ((4 * n : ℕ) : ℝ) := by
      have := abs_nonneg C
      linarith
    rw [div_le_iff₀ hc₇] at hL
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- From an exit site of `C_n` the segment `[n, 2n)` is visited before the origin.
  have hgood : ∀ w : Site 2, (n : ℝ) ≤ euclidNorm w → euclidNorm w < n + 1 →
      ENNReal.ofReal (c₇ / 2) ≤ siteWalkLaw 2 w (segmentPath (4 * n)) := by
    intro w hw₁ hw₂
    have ha := h₇ (4 * n) (by omega) _ isDense_axisSet_nonneg w (by rw [h4n]; linarith)
    have hb := (h₈ (4 * n) (by omega) w (by rw [h4n]; linarith) (by rw [h4n]; linarith)).2
    rw [← pathLaw_preimage w (measurableSet_segmentPath _),
      ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    set S := shellPart (axisSet {j | 0 ≤ j}) (((4 * n : ℕ) : ℝ) / 4) (((4 * n : ℕ) : ℝ) / 2)
    have e : (fun ω => walkPos w ω) ⁻¹' segmentPath (4 * n) =
        hitsBefore S ((4 * n : ℕ) : ℝ) w \ hitsBefore {0} ((4 * n : ℕ) : ℝ) w := rfl
    have hle := (measure_mono (μ := pathLaw 2)
      (Set.subset_sdiff_union (hitsBefore S ((4 * n : ℕ) : ℝ) w)
        (hitsBefore {0} ((4 * n : ℕ) : ℝ) w))).trans (measure_union_le _ _)
    have hle' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hle'
    rw [e]
    simp only [prob] at ha hb
    linarith
  -- The decomposition at the first exit time from `C_n`.
  have hPm : ∀ p : ℕ × Site 2, MeasurableSet (firstExitPath n p.2 p.1) :=
    fun p => measurableSet_firstExitPath _ _ _
  have hQm : ∀ p : ℕ × Site 2,
      MeasurableSet (firstExitPath n p.2 p.1 ∩ shiftPath p.1 ⁻¹' segmentPath (4 * n)) :=
    fun p => (hPm p).inter ((measurableSet_segmentPath _).preimage (measurable_shiftPath _))
  have hdisjP := pairwise_disjoint_firstExitPath (n : ℝ)
  have hdisjQ : Pairwise (Function.onFun Disjoint fun p : ℕ × Site 2 =>
      firstExitPath n p.2 p.1 ∩ shiftPath p.1 ⁻¹' segmentPath (4 * n)) :=
    fun p q h => (hdisjP h).mono Set.inter_subset_left Set.inter_subset_left
  set F := (fun ω => walkPos 0 ω) ⁻¹'
    ⋃ p : ℕ × Site 2, firstExitPath n p.2 p.1 ∩ shiftPath p.1 ⁻¹' segmentPath (4 * n) with hFdef
  have hFm : MeasurableSet F := (MeasurableSet.iUnion hQm).preimage (measurable_walkPath 0)
  have h1 : pathLaw 2 F = ∑' p : ℕ × Site 2,
      siteWalkLaw 2 0 (firstExitPath n p.2 p.1) * siteWalkLaw 2 p.2 (segmentPath (4 * n)) := by
    rw [hFdef, pathLaw_preimage 0 (MeasurableSet.iUnion hQm), measure_iUnion hdisjQ hQm]
    exact tsum_congr fun p => siteWalkLaw_inter_shift 0 p.2 p.1 (hPm p)
      (measurableSet_segmentPath _) firstExitPath_congr fun X hX => hX.2.2.1
  have h2 : ENNReal.ofReal (c₇ / 2) * pathLaw 2 (exitsBefore n {0} 0) ≤ pathLaw 2 F := by
    rw [h1]
    calc ENNReal.ofReal (c₇ / 2) * pathLaw 2 (exitsBefore n {0} 0)
        ≤ ENNReal.ofReal (c₇ / 2) *
            ∑' p : ℕ × Site 2, siteWalkLaw 2 0 (firstExitPath n p.2 p.1) := by
          gcongr
          rw [← measure_iUnion hdisjP hPm, ← pathLaw_preimage 0 (MeasurableSet.iUnion hPm)]
          exact measure_mono (exitsBefore_subset hn0)
      _ = ∑' p : ℕ × Site 2,
            siteWalkLaw 2 0 (firstExitPath n p.2 p.1) * ENNReal.ofReal (c₇ / 2) := by
          rw [ENNReal.tsum_mul_right, mul_comm]
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun p => ?_
          by_cases hp : (n : ℝ) ≤ euclidNorm p.2 ∧ euclidNorm p.2 < n + 1
          · gcongr
            exact hgood p.2 hp.1 hp.2
          · have : firstExitPath n p.2 p.1 = ∅ :=
              Set.eq_empty_of_forall_notMem fun X hX => hp ⟨hX.1, hX.2.1⟩
            simp [this]
  have hE : entersAt ({axisPt (-n)} ∪ axisSet {j | 0 ≤ j}) (axisPt (-n)) (axisPt (-n)) ⊆ Fᶜ := by
    intro ω hω hF
    simp only [hFdef, Set.mem_preimage, Set.mem_iUnion] at hF
    obtain ⟨p, hP, hS⟩ := hF
    exact not_mem_entersAt hn0 hP hS hω
  have hprobE : prob (entersAt ({axisPt (-n)} ∪ axisSet {j | 0 ≤ j}) (axisPt (-n)) (axisPt (-n)))
      ≤ 1 - prob F := by
    have h := measure_mono (μ := pathLaw 2) hE
    rw [prob_compl_eq_one_sub hFm] at h
    calc _ ≤ (1 - pathLaw 2 F).toReal := ENNReal.toReal_mono (by simp) h
      _ = 1 - prob F := by
          rw [ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, prob]
  have hprobF : c₇ / 2 * prob (exitsBefore n {0} 0) ≤ prob F := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  -- The escape probability is at least `π / (4 log n)`.
  have hG := green_mul_prob_exitsBefore hnR
  have hGC := (hC n hn2).2
  have hp0 : 0 ≤ prob (exitsBefore n {0} 0) := ENNReal.toReal_nonneg
  have hπG : Real.pi * green n 0 0 ≤ 4 * Real.log n := by
    have := le_abs_self C
    have := (abs_le.1 hGC).2
    linarith
  have hp : Real.pi / (4 * Real.log n) ≤ prob (exitsBefore n {0} 0) := by
    rw [div_le_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_left hπG hp0
    have e : prob (exitsBefore n {0} 0) * (Real.pi * green n 0 0) = Real.pi := by
      rw [show prob (exitsBefore n {0} 0) * (Real.pi * green n 0 0)
          = Real.pi * (green n 0 0 * prob (exitsBefore n {0} 0)) by ring, hG, mul_one]
    linarith
  have hfin : c₇ * Real.pi / 8 / Real.log n = c₇ / 2 * (Real.pi / (4 * Real.log n)) := by
    field_simp
    ring
  rw [hfin]
  have := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ c₇ / 2)
  linarith

end FiniteAvalanches.Walk.Beurling
