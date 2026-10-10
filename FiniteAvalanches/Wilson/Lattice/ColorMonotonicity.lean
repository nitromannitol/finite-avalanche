import FiniteAvalanches.Wilson.Lattice.Law
import FiniteAvalanches.Statements.ForestColorMonotonicity
import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Trees.Lattice FiniteAvalanches.Sandpile MeasureTheory Filter
open scoped Classical
noncomputable section

/-- A literal event depending only on the colors of a finite vertex window. -/
def windowColorEvent (W : Finset (Site 2)) (H : Set (W → Bool)) : Set ColorField :=
  {σ | (fun x : W => σ x.val) ∈ H}

theorem isClopen_windowColorEvent (W : Finset (Site 2)) (H : Set (W → Bool)) :
    IsClopen (windowColorEvent W H) :=
  (isClopen_discrete H).preimage (continuous_pi fun x => continuous_apply x.val)

/-- The same finite event read on the true wired-site projection. -/
def wiredWindowEvent (N : ℕ) (W : Finset (Site 2)) (H : Set (W → Bool)) :
    Set (Set (FiniteWired.Vertex N)) :=
  {U | (fun x : W => decide (wiredSite N x.val ∈ U)) ∈ H}

theorem wiredWindowEvent_increasing (N : ℕ) (W : Finset (Site 2)) (H : Set (W → Bool))
    (hH : ∀ p ∈ H, ∀ q : W → Bool, (∀ x, p x = true → q x = true) → q ∈ H) :
    ∀ U ∈ wiredWindowEvent N W H, ∀ V, U ⊆ V → V ∈ wiredWindowEvent N W H := by
  intro U hU V hUV
  apply hH _ hU
  intro x hx
  exact decide_eq_true (hUV (of_decide_eq_true hx))

theorem finite_window_real_count (R : RootPair) (N : ℕ) (W : Finset (Site 2))
    (H : Set (W → Bool)) :
    (finiteForestLaw R N).real (Prod.snd ⁻¹' windowColorEvent W H) =
      (Nat.card {f : FiniteForest R N |
        (WiredTrees.graph N).oneVertices f.val (wiredOne R N) ∈ wiredWindowEvent N W H} : ℝ) /
        Nat.card (FiniteForest R N) := by
  have hm : MeasurableSet (Prod.snd ⁻¹' windowColorEvent W H : Set ForestField) :=
    ((isClopen_windowColorEvent W H).preimage continuous_snd).isClosed.measurableSet
  rw [Measure.real, finiteForestLaw_count R N _ hm]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, finiteForestCount]
  have he : ({f : FiniteForest R N |
      finiteForestField R N f ∈ Prod.snd ⁻¹' windowColorEvent W H} : Set (FiniteForest R N)) =
      {f : FiniteForest R N |
        (WiredTrees.graph N).oneVertices f.val (wiredOne R N) ∈ wiredWindowEvent N W H} := by
    ext f
    change (fun x : W => finiteColors R N f (wiredSite N x.val)) ∈ H ↔
      (fun x : W => decide (wiredSite N x.val ∈
        (WiredTrees.graph N).oneVertices f.val (wiredOne R N))) ∈ H
    have hc : (fun x : W => finiteColors R N f (wiredSite N x.val)) =
        (fun x : W => decide (wiredSite N x.val ∈
          (WiredTrees.graph N).oneVertices f.val (wiredOne R N))) := by
      funext x
      unfold finiteColors
      apply Bool.decide_congr
      rfl
    rw [hc]
  rw [he]

theorem finite_window_real_tendsto (R : RootPair) (W : Finset (Site 2))
    (H : Set (W → Bool)) :
    Tendsto (fun N => (finiteForestLaw R N).real (Prod.snd ⁻¹' windowColorEvent W H))
      atTop (nhds ((wilsonColorLaw R).real (windowColorEvent W H))) := by
  have hc : IsClopen (Prod.snd ⁻¹' windowColorEvent W H : Set ForestField) :=
    (isClopen_windowColorEvent W H).preimage continuous_snd
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (finiteForestProbability_tendsto R) (E := Prod.snd ⁻¹' windowColorEvent W H)
    (by simp [hc])
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (wilsonLaw R : Measure ForestField) _)).comp ht
  have he : (wilsonColorLaw R).real (windowColorEvent W H) =
      (wilsonLaw R : Measure ForestField).real (Prod.snd ⁻¹' windowColorEvent W H) := by
    rw [Measure.real, wilsonColorLaw, Measure.map_apply measurable_snd
      (isClopen_windowColorEvent W H).isClosed.measurableSet]
    rfl
  rw [he]
  exact hr

theorem eventually_inBox (x : Site 2) : ∀ᶠ N : ℕ in atTop, FiniteWired.inBox N x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|x 0| + |x 1| : ℤ)
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hcast : (N : ℤ) ≤ n := Int.ofNat_le.mpr hn
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  have hp0 := le_abs_self (x 0)
  have hp1 := le_abs_self (x 1)
  have hn0 := neg_abs_le (x 0)
  have hn1 := neg_abs_le (x 1)
  intro i
  fin_cases i
  · change -(n : ℤ) ≤ x 0 ∧ x 0 ≤ n
    constructor <;> omega
  · change -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n
    constructor <;> omega

theorem wiredZero_eventually_nonempty (R : RootPair) :
    ∀ᶠ N : ℕ in atTop, (wiredZero R N).Nonempty := by
  obtain ⟨a, ha⟩ := R.zero_nonempty
  filter_upwards [eventually_inBox a] with N hN
  exact ⟨some (FiniteWired.activeOfSite N a hN), ha⟩

theorem wired_graph_connected (N : ℕ) :
    ∀ x y, (WiredTrees.graph N).reaches Finset.univ x y := by
  intro x y
  exact (WiredTrees.graph N).reaches_mono (Finset.subset_univ _)
    ((WiredTrees.rowTree N).property.2.2.1 x (Set.mem_univ x) y (Set.mem_univ y))

/-- Full finite-window comparison when any one roots are removed. -/
theorem color_window_one_roots_removed (R Q : RootPair)
    (hz : Q.zero = R.zero) (ho : Q.one ⊆ R.one)
    (W : Finset (Site 2)) (H : Set (W → Bool))
    (hH : ∀ p ∈ H, ∀ q : W → Bool, (∀ x, p x = true → q x = true) → q ∈ H) :
    (wilsonColorLaw Q).real (windowColorEvent W H) ≤
      (wilsonColorLaw R).real (windowColorEvent W H) := by
  apply le_of_tendsto_of_tendsto (finite_window_real_tendsto Q W H)
    (finite_window_real_tendsto R W H)
  filter_upwards [wiredZero_eventually_nonempty R] with N hN
  have hzN : wiredZero Q N = wiredZero R N := by
    ext v
    cases v with
    | none => rfl
    | some x =>
      change FiniteWired.site x ∈ Q.zero ↔ FiniteWired.site x ∈ R.zero
      rw [hz]
  have hoN : wiredOne Q N ⊆ wiredOne R N := by
    intro v hv
    cases v with
    | none => trivial
    | some x => exact ho hv
  have hfin := ((FiniteAvalanches.Statements.forest_color_monotonicity (WiredTrees.graph N)
    (wired_graph_connected N) (wiredZero R N) (wiredOne R N)
    (wired_roots_disjoint R N) hN ⟨none, trivial⟩).1
      (wiredOne Q N) hoN ⟨none, trivial⟩).1
      (wiredWindowEvent N W H) (wiredWindowEvent_increasing N W H hH)
  rw [finite_window_real_count, finite_window_real_count]
  let ratio (A C : Set (FiniteWired.Vertex N)) : ℝ :=
    (Nat.card {f : (WiredTrees.graph N).RootedForest (A ∪ C) |
      (WiredTrees.graph N).oneVertices f.val C ∈ wiredWindowEvent N W H} : ℝ) /
      Nat.card ((WiredTrees.graph N).RootedForest (A ∪ C))
  change ratio (wiredZero Q N) (wiredOne Q N) ≤ ratio (wiredZero R N) (wiredOne R N)
  rw [hzN]
  exact hfin

/-- Full finite-window comparison when any zero roots are added outside the one roots. -/
theorem color_window_zero_roots_added (R Q : RootPair)
    (hz : R.zero ⊆ Q.zero) (ho : Q.one = R.one)
    (W : Finset (Site 2)) (H : Set (W → Bool))
    (hH : ∀ p ∈ H, ∀ q : W → Bool, (∀ x, p x = true → q x = true) → q ∈ H) :
    (wilsonColorLaw Q).real (windowColorEvent W H) ≤
      (wilsonColorLaw R).real (windowColorEvent W H) := by
  apply le_of_tendsto_of_tendsto (finite_window_real_tendsto Q W H)
    (finite_window_real_tendsto R W H)
  filter_upwards [wiredZero_eventually_nonempty R] with N hN
  have hoN : wiredOne Q N = wiredOne R N := by
    ext v
    cases v with
    | none => rfl
    | some x =>
      change FiniteWired.site x ∈ Q.one ↔ FiniteWired.site x ∈ R.one
      rw [ho]
  have hzN : wiredZero R N ⊆ wiredZero Q N := by
    intro v hv
    cases v with
    | none => exact False.elim hv
    | some x => exact hz hv
  have hdN : Disjoint (wiredZero Q N) (wiredOne R N) := by
    rw [← hoN]
    exact wired_roots_disjoint Q N
  have hfin := ((FiniteAvalanches.Statements.forest_color_monotonicity (WiredTrees.graph N)
    (wired_graph_connected N) (wiredZero R N) (wiredOne R N)
    (wired_roots_disjoint R N) hN ⟨none, trivial⟩).2
      (wiredZero Q N) hzN hdN).1
      (wiredWindowEvent N W H) (wiredWindowEvent_increasing N W H hH)
  rw [finite_window_real_count, finite_window_real_count]
  let ratio (A C : Set (FiniteWired.Vertex N)) : ℝ :=
    (Nat.card {f : (WiredTrees.graph N).RootedForest (A ∪ C) |
      (WiredTrees.graph N).oneVertices f.val C ∈ wiredWindowEvent N W H} : ℝ) /
      Nat.card ((WiredTrees.graph N).RootedForest (A ∪ C))
  change ratio (wiredZero Q N) (wiredOne Q N) ≤ ratio (wiredZero R N) (wiredOne R N)
  rw [hoN]
  exact hfin

/-- Source fo:lattice-monotonicity: both operations, all original roots and every
increasing event of the full joint color pattern on every finite vertex window. -/
theorem lattice_color_monotonicity :
    (∀ (R Q : RootPair), Q.zero = R.zero → Q.one ⊆ R.one →
      ∀ (W : Finset (Site 2)) (H : Set (W → Bool)),
        (∀ p ∈ H, ∀ q : W → Bool, (∀ x, p x = true → q x = true) → q ∈ H) →
        (wilsonColorLaw Q).real (windowColorEvent W H) ≤
          (wilsonColorLaw R).real (windowColorEvent W H)) ∧
    (∀ (R Q : RootPair), R.zero ⊆ Q.zero → Q.one = R.one →
      ∀ (W : Finset (Site 2)) (H : Set (W → Bool)),
        (∀ p ∈ H, ∀ q : W → Bool, (∀ x, p x = true → q x = true) → q ∈ H) →
        (wilsonColorLaw Q).real (windowColorEvent W H) ≤
          (wilsonColorLaw R).real (windowColorEvent W H)) :=
  ⟨color_window_one_roots_removed, color_window_zero_roots_added⟩

end
end FiniteAvalanches.Wilson.Lattice
