import FiniteAvalanches.Walk.Beurling.Defs
import LatticeProb.Walk.RecurrenceHitting
import LatticeProb.Graph.ExitDecomp

/-!
# The Green function of a disk counts expected visits

For a finite set `B ⊆ ℤ²`, four times the killed Green function of the library is the expected
number of visits to `z` of the simple random walk started at `w` before it leaves `B`:
`4 g_B(w, z) = E_w[∑_t 1{S_0, …, S_t ∈ B, S_t = z}]`, the degree `4` of `ℤ²` being the
normalization of `Graph.killedGreenReal`. This is formula (6) of G. F. Lawler and V. Limic,
*The Beurling estimate for a class of random walks*, Electron. J. Probab. 9 (2004). At
`B = C_r` it says that `green r w z` is the expected number of visits to `z` before the walk
leaves the disk `C_r`.

The `t`-step killed kernel is the probability that the walk stays in `B` up to time `t` and is
at `z` at time `t`, by the Markov property at time one; summing over `t` gives the formula.

## Main statements

* `ofReal_killedGreenReal_eq`: `4 g_B(w, z)` is the expected number of visits to `z` before
  the walk leaves `B`.
* `green_eq_tsum_visits`: `green r w z` is the expected number of visits to `z` before the walk
  leaves `C_r`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

/-- The paths that stay in `B` up to time `t` and are at `z` at time `t`. -/
private def stayAt (B : Set (Site 2)) (z : Site 2) (t : ℕ) : Set (ℕ → Site 2) :=
  {X | (∀ s ≤ t, X s ∈ B) ∧ X t = z}

private theorem measurableSet_stayAt (B : Set (Site 2)) (z : Site 2) (t : ℕ) :
    MeasurableSet (stayAt B z t) :=
  measurableSet_setOf.2 <|
    (Measurable.forall fun s => (measurable_of_countable fun y : Site 2 => s ≤ t → y ∈ B).comp
      (measurable_pi_apply s)).and
    ((measurable_of_countable fun y : Site 2 => y = z).comp (measurable_pi_apply t))

/-- The killed kernel is the law of the walk on the event of survival:
`P_w(S_0, …, S_t ∈ B, S_t = z) = p^B_t(w, z)`. -/
private theorem siteWalkLaw_real_stayAt (B : Set (Site 2)) (z : Site 2) :
    ∀ (t : ℕ) (w : Site 2),
      (siteWalkLaw 2 w).real (stayAt B z t) = Graph.killedHeat (lattice 2) B t w z := by
  classical
  have hstart : ∀ w : Site 2, ∀ᵐ X ∂(siteWalkLaw 2 w), X 0 = w := by
    intro w
    rw [siteWalkLaw_eq, ae_map_iff (measurable_sitePath w).aemeasurable
      (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)]
    exact Filter.Eventually.of_forall fun ξ => sitePath_zero w ξ
  intro t
  induction t with
  | zero =>
    intro w
    have h : ∀ᵐ X ∂(siteWalkLaw 2 w), (stayAt B z 0).indicator (1 : (ℕ → Site 2) → ℝ) X
        = Graph.killedHeat (lattice 2) B 0 w z := by
      filter_upwards [hstart w] with X hX
      rw [Network.killedHeat_zero]
      by_cases hw : w ∈ B <;> by_cases hwz : w = z <;>
        simp [stayAt, Set.indicator_apply, hX, hw, hwz]
    rw [← integral_indicator_one (measurableSet_stayAt B z 0), integral_congr_ae h,
      integral_const, probReal_univ, one_smul]
  | succ t ih =>
    intro w
    set F : (ℕ → Site 2) → ℝ := (stayAt B z t).indicator 1 with hF
    have hFm : Measurable F := measurable_one.indicator (measurableSet_stayAt B z t)
    have hFb : ∀ X, ‖F X‖ ≤ 1 := fun X => by
      rw [hF, Set.indicator_apply]
      split_ifs <;> simp
    have hpe : pathExpect 2 F = fun y => Graph.killedHeat (lattice 2) B t y z := by
      funext y
      rw [pathExpect, hF, integral_indicator_one (measurableSet_stayAt B z t), ih y]
    have h : ∀ᵐ X ∂(siteWalkLaw 2 w), (stayAt B z (t + 1)).indicator (1 : (ℕ → Site 2) → ℝ) X
        = (if w ∈ B then 1 else 0) * F (shiftPath 1 X) := by
      filter_upwards [hstart w] with X hX
      have hiff : X ∈ stayAt B z (t + 1) ↔ w ∈ B ∧ shiftPath 1 X ∈ stayAt B z t := by
        simp only [stayAt, Set.mem_setOf_eq, shiftPath]
        constructor
        · rintro ⟨hB, hz⟩
          refine ⟨hX ▸ hB 0 (Nat.zero_le _), fun s hs => hB (1 + s) (by omega), ?_⟩
          rw [add_comm]
          exact hz
        · rintro ⟨hw, hB, hz⟩
          refine ⟨fun s hs => ?_, by rw [add_comm] at hz; exact hz⟩
          rcases s with _ | s
          · exact hX ▸ hw
          · have := hB s (by omega)
            rwa [add_comm] at this
      rw [hF]
      by_cases hw : w ∈ B
      · simp [Set.indicator_apply, hiff, hw]
      · simp [Set.indicator_apply, hiff, hw]
    rw [← integral_indicator_one (measurableSet_stayAt B z (t + 1)), integral_congr_ae h,
      integral_const_mul, integral_comp_shiftPath 2 1 w F hFm hFb, hpe, Function.iterate_one,
      Graph.Zd.killedHeat_succ_walkOp]
    by_cases hw : w ∈ B <;> simp [hw]

/-- The probability under the path law that the walk started at `w` stays in `B` up to time
`t` and is at `z` at time `t` is the killed kernel `p^B_t(w, z)`. -/
private theorem pathLaw_stay_eq (B : Set (Site 2)) (w z : Site 2) (t : ℕ) :
    pathLaw 2 {ω | (∀ s ≤ t, walkPos w ω s ∈ B) ∧ walkPos w ω t = z}
      = ENNReal.ofReal (Graph.killedHeat (lattice 2) B t w z) := by
  have hmeas : Measurable fun ω : ℕ → Dir 2 => walkPos w ω :=
    measurable_pi_lambda _ fun t => measurable_walkPos w t
  have hmap : (pathLaw 2).map (fun ω => walkPos w ω) = siteWalkLaw 2 w :=
    pathLaw_map_sitePath 2 w
  have hpre : {ω | (∀ s ≤ t, walkPos w ω s ∈ B) ∧ walkPos w ω t = z}
      = (fun ω => walkPos w ω) ⁻¹' stayAt B z t := rfl
  rw [hpre, ← Measure.map_apply hmeas (measurableSet_stayAt B z t), hmap,
    ← siteWalkLaw_real_stayAt B z t w, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Lawler-Limic (6).** Four times the killed Green function of a finite set `B` is the
expected number of visits to `z` of the walk started at `w` before it leaves `B`. -/
theorem ofReal_killedGreenReal_eq (B : Finset (Site 2)) (w z : Site 2) :
    ENNReal.ofReal (4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) w z) =
      ∫⁻ ω, ∑' t, ({ω | (∀ s ≤ t, walkPos w ω s ∈ B) ∧ walkPos w ω t = z}.indicator 1 ω)
        ∂pathLaw 2 := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
  have hnn : ∀ t, 0 ≤ Graph.killedHeat (lattice 2) (B : Set (Site 2)) t w z :=
    fun t => Network.killedHeat_nonneg _ t w z
  have hsum := Network.summable_killedHeat (Graph.Zd.latticeConnected 2) B hq w z
  have hW : Measurable fun ω : ℕ → Dir 2 => walkPos w ω :=
    measurable_pi_lambda _ fun t => measurable_walkPos w t
  have hmeas : ∀ t, MeasurableSet
      {ω : ℕ → Dir 2 | (∀ s ≤ t, walkPos w ω s ∈ B) ∧ walkPos w ω t = z} := fun t =>
    (measurableSet_stayAt (B : Set (Site 2)) z t).preimage hW
  have hterm : ∀ t, ∫⁻ ω, {ω | (∀ s ≤ t, walkPos w ω s ∈ B) ∧ walkPos w ω t = z}.indicator 1 ω
      ∂pathLaw 2 = ENNReal.ofReal (Graph.killedHeat (lattice 2) (B : Set (Site 2)) t w z) :=
    fun t => by
      rw [lintegral_indicator_one (hmeas t)]
      exact pathLaw_stay_eq (B : Set (Site 2)) w z t
  rw [lintegral_tsum fun t => (measurable_one.indicator (hmeas t)).aemeasurable,
    tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum,
    Network.killedGreenReal_eq_tsum (Graph.Zd.latticeConnected 2) B hq w z, Graph.Zd.degree_eq]
  congr 1
  push_cast
  ring

/-- **Lawler-Limic (6) for the disk.** `green r w z` is the expected number of visits to `z` of
the walk started at `w` before it leaves the disk `C_r`. -/
theorem green_eq_tsum_visits (r : ℝ) (w z : Site 2) : ENNReal.ofReal (green r w z) = ∫⁻ ω, ∑' t,
    ({ω | (∀ s ≤ t, walkPos w ω s ∈ diskFinset r) ∧ walkPos w ω t = z}.indicator 1 ω)
      ∂pathLaw 2 :=
  ofReal_killedGreenReal_eq (diskFinset r) w z

end FiniteAvalanches.Walk.Beurling
