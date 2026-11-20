import FiniteAvalanches.Support.Plane.PerfectLocalCantor
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli

/-!
# A diffuse measure on Cantor space

The fair-coin product measure gives every point of Cantor space measure zero.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The fair-coin probability measure on Cantor space. -/
noncomputable def cantorCoinMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false ⟨1 / 2, by norm_num⟩)

/-- Every Cantor-space point has measure zero under the fair-coin product. -/
theorem cantorCoinMeasure_singleton (f : ℕ → Bool) : cantorCoinMeasure {f} = 0 := by
  have hcoord : ∀ b : Bool,
      bernoulliMeasure true false ⟨1 / 2, by norm_num⟩ {b} = (1 / 2 : ℝ≥0∞) := by
    intro b
    have hh : ((1 / 2 : NNReal) : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by norm_num
    cases b <;> norm_num [bernoulliMeasure_apply, unitInterval.toNNReal, unitInterval.symm]
    all_goals
      simp only [one_div] at hh
      rw [← hh]
      apply ENNReal.coe_inj.mpr
      apply Subtype.ext
      norm_num [NNReal.coe_mk, NNReal.coe_inv, unitInterval.toNNReal, unitInterval.symm]
  have hbound : ∀ n : ℕ, cantorCoinMeasure {f} ≤ (1 / 2 : ℝ≥0∞) ^ n := by
    intro n
    have hsub : ({f} : Set (ℕ → Bool)) ⊆ (↑(Finset.range n) : Set ℕ).pi (fun i => {f i}) := by
      rintro g rfl
      intro i hi
      exact mem_singleton _
    calc
      cantorCoinMeasure {f} ≤ cantorCoinMeasure ((↑(Finset.range n) : Set ℕ).pi (fun i => {f i})) :=
        measure_mono hsub
      _ = (1 / 2 : ℝ≥0∞) ^ n := by
        change (Measure.infinitePi (fun _ : ℕ =>
          bernoulliMeasure true false ⟨1 / 2, by norm_num⟩))
            ((↑(Finset.range n) : Set ℕ).pi (fun i => {f i})) = _
        have h := Measure.infinitePi_pi
          (fun _ : ℕ => bernoulliMeasure true false ⟨1 / 2, by norm_num⟩)
          (s := Finset.range n) (t := fun i => {f i})
          (fun _ _ => measurableSet_singleton _)
        simpa only [hcoord, Finset.prod_const, Finset.card_range] using h
  apply le_antisymm _ bot_le
  exact ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)) hbound

/-- A perfect set carries a diffuse probability concentrated inside any
open set meeting it. -/
theorem Perfect.exists_diffuse_probability_in_open
    {X : Type*} [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    {K U : Set X} (hK : Perfect K) (hU : IsOpen U) (hne : (U ∩ K).Nonempty) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ (∀ x, μ {x} = 0) ∧ μ (U ∩ K) = 1 := by
  obtain ⟨f, hfsub, hfc, hfi⟩ := Perfect.exists_nat_bool_injection_in_open hK hU hne
  haveI : IsProbabilityMeasure cantorCoinMeasure := by
    unfold cantorCoinMeasure
    infer_instance
  have hfmeas : Measurable f := hfc.measurable
  haveI : IsProbabilityMeasure (cantorCoinMeasure.map f) :=
    Measure.isProbabilityMeasure_map hfmeas.aemeasurable
  refine ⟨cantorCoinMeasure.map f, inferInstance, ?_, ?_⟩
  · intro x
    rw [Measure.map_apply hfmeas (measurableSet_singleton x)]
    by_cases hx : x ∈ range f
    · obtain ⟨a, rfl⟩ := hx
      have heq : f ⁻¹' {f a} = {a} := by
        ext z
        simp only [mem_preimage, mem_singleton_iff]
        exact hfi.eq_iff
      rw [heq, cantorCoinMeasure_singleton]
    · have heq : f ⁻¹' {x} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hx ⟨z, hz⟩
      simp only [heq, measure_empty]
  · rw [Measure.map_apply hfmeas (hU.measurableSet.inter hK.closed.measurableSet)]
    have heq : f ⁻¹' (U ∩ K) = univ := by
      apply Set.eq_univ_of_forall
      intro z
      exact hfsub ⟨z, rfl⟩
    rw [heq, measure_univ]

end FiniteAvalanches.Electrical.StatementGeometry
