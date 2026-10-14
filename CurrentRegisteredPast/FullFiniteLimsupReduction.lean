import FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors
import FiniteAvalanches.Trees.Lattice.PastEscapeLimits
import CurrentRootConsumers.PastTail
import FiniteAvalanches.Sandpile.SourceCounting.CurrentCountingApplication
import FiniteAvalanches.Sandpile.Source.RadiusConnector
import FiniteAvalanches.Sandpile.Law.BoxLimit
import FiniteAvalanches.Probability.Radius.RealThresholds
import Mathlib.Topology.Order.LiminfLimsup

/-! Finite-volume radius reduction through the original vertex past sum and its cylinder limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Paper.RegisteredPast.RadiusReductionFull

open LatticeProb FiniteAvalanches Sandpile SourceCounting Components MeasureTheory Filter
open Trees.Lattice TreeMeasurability11 Trees.Lattice.CurrentPastCylinder
open SourceCounting.CurrentPastVertices SourceCounting.CurrentTailErrors
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal BigOperators
noncomputable section

/-- The actual finite field radius is bounded by the reciprocal and the original
vertex past escape sum, with no assumed finite-volume estimate. -/
theorem finite_radius_le_reciprocal_add_vertex_pasts {N r M : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (hMN : M + 1 ≤ N) :
    (FiniteWired.finiteFieldLaw N).real {η | (M : WithTop ℕ) < radius η 0} ≤
      (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) +
      ∑ x ∈ sourceVertices r, (WiredTrees.law N).real
        (finitePastEvent x (boxSites M) N)ᶜ := by
  have hfinite := SourceCounting.CurrentFront.finiteFieldLaw_origin_radius_probability_le hr hrN hMN
  have hexpect :
      (∫ t, WiredTrees.reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t ∂WiredTrees.law N) =
      ∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂WiredTrees.law N := by
    apply integral_congr_ae
    exact Eventually.of_forall fun t => Source.finite_reciprocal_eq_finiteZN hr hrN t
  rw [hexpect] at hfinite
  exact hfinite.trans (add_le_add le_rfl
    (source_edge_error_sum_le_vertex_past_sum N r M hr hrN))

/-- The finite reciprocal is bounded on every actual copied-tree outcome. -/
theorem finite_reciprocal_bounds (N : ℕ) (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : (WiredTrees.graph N).SpanningTree) :
    0 ≤ finiteZN N S hS t ∧ finiteZN N S hS t ≤ 1 := by
  unfold finiteZN
  split
  · exact (WiredTrees.graph N).reciprocalWeight_one_nonneg_le_one none (finiteMarks N S)
      (finiteMarks_nonempty N S hS ‹∀ x ∈ S, FiniteWired.inBox N x›) t
  · exact ⟨le_rfl, zero_le_one⟩

theorem finite_reciprocal_expectation_le_one (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) :
    (∫ t, finiteZN N S hS t ∂WiredTrees.law N) ≤ 1 := by
  have h := integral_mono_of_nonneg
    (Eventually.of_forall fun t => (finite_reciprocal_bounds N S hS t).1)
    (integrable_const (μ := WiredTrees.law N) (1 : ℝ))
    (Eventually.of_forall fun t => (finite_reciprocal_bounds N S hS t).2)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

/-- A bounded reciprocal needs no expectation limit: subtract only the convergent error sum. -/
theorem le_limsup_add_of_eventual_bound {a e b : ℕ → ℝ} {A B : ℝ}
    (ha : Tendsto a atTop (nhds A)) (hb : Tendsto b atTop (nhds B))
    (he : IsBoundedUnder (· ≤ ·) atTop e)
    (hle : ∀ᶠ N : ℕ in atTop, a N ≤ e N + b N) :
    A ≤ limsup e atTop + B := by
  have hlim : Tendsto (fun N => a N - b N) atTop (nhds (A - B)) := ha.sub hb
  have h : A - B ≤ limsup e atTop := by
    apply le_limsup_of_le he
    intro c hc
    apply le_of_tendsto hlim
    filter_upwards [hle, hc] with N hN hNc
    linarith only [hN, hNc]
  linarith only [h]

/-- One universal constant controls the finite limiting sum over the actual r+4 sites. -/
theorem reciprocal_reduction_limsup_current :
    ∃ C : ℝ, ∀ r : ℕ, 2 ≤ r → ∀ M : ℕ, r + 2 ≤ M →
      (infiniteVolumeLaw : Measure StableField).real
        {η | ENNReal.ofReal (M : ℝ) < extendedCount (radius η 0)} ≤
        (limsup (fun N : ℕ => ∫ t, finiteZN N (sourceMarks r)
          (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) atTop) +
        C * (r : ℝ) * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C, hC, htail⟩ :=
    FiniteAvalanches.Paper.CurrentRootConsumers.registered_past_complement_bound
  refine ⟨3 * C, ?_⟩
  intro r hr M hM
  have ha := (ENNReal.tendsto_toReal (measure_ne_top (infiniteVolumeLaw : Measure StableField)
    {η | (M : WithTop ℕ) < radius η 0})).comp
      (Probability.tendsto_radius_gt_of_weak infiniteVolumeLaw
        tendsto_finiteFieldProbability_infiniteVolumeLaw 0 M)
  have hb := tendsto_finsetSum (sourceVertices r)
    (fun x _ => CurrentRadiusReduction.finite_past_escape_real_tendsto x (boxSites M))
  have he : IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ =>
      ∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) := by
    apply isBoundedUnder_of_eventually_le (a := (1 : ℝ))
    exact Eventually.of_forall fun N => finite_reciprocal_expectation_le_one N _ _
  have hfinite : ∀ᶠ N : ℕ in atTop,
      (FiniteWired.finiteFieldLaw N).real {η | (M : WithTop ℕ) < radius η 0} ≤
        (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) +
        ∑ x ∈ sourceVertices r, (WiredTrees.law N).real
          (finitePastEvent x (boxSites M) N)ᶜ := by
    filter_upwards [eventually_ge_atTop (M + 1)] with N hN
    exact finite_radius_le_reciprocal_add_vertex_pasts hr (by omega) hN
  have hreduce := le_limsup_add_of_eventual_bound ha hb he hfinite
  have hsum :
      (∑ x ∈ sourceVertices r, (squareLatticeUST : Measure EdgeField).real
        (infinitePastEvent x (boxSites M))ᶜ) ≤
        (3 * C) * (r : ℝ) * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
    calc
      _ ≤ ∑ _x ∈ sourceVertices r, C * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) :=
        Finset.sum_le_sum fun x hx => htail r M hM x (sourceVertices_subset_box r hr hx)
      _ = ((r : ℝ) + 4) * (C * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ))) := by
        rw [Finset.sum_const, card_sourceVertices r hr]
        simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
      _ ≤ (3 * (r : ℝ)) * (C * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ))) := by
        apply mul_le_mul_of_nonneg_right
        · have hrreal : 2 ≤ (r : ℝ) := by exact_mod_cast hr
          linarith only [hrreal]
        · exact mul_nonneg hC.le (Real.rpow_nonneg (by
            exact_mod_cast (show (0 : ℤ) ≤ (M : ℤ) - (r : ℤ) by omega)) _)
      _ = _ := by ring
  rw [Probability.real_radius_tail_eq_floor 0 (M : ℝ) (by positivity), Nat.floor_natCast]
  exact hreduce.trans (add_le_add le_rfl hsum)

end
end FiniteAvalanches.Paper.RegisteredPast.RadiusReductionFull

#print axioms FiniteAvalanches.Paper.RegisteredPast.RadiusReductionFull.reciprocal_reduction_limsup_current
