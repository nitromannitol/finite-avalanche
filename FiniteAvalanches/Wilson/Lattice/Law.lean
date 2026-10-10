import FiniteAvalanches.External.ColoredWilson

/-! The source law is selected only after the full unique-existence declaration.
All results are relative to that registered standard input. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Trees.Lattice MeasureTheory
open scoped Classical
noncomputable section

/-- Selected ONLY from the complete unique-law standard characterization above.
The complete characterization is registered with the selected law. -/
def wilsonLaw (R : RootPair) : ProbabilityMeasure ForestField :=
  Classical.choose (FiniteAvalanches.External.wilson_two_color_law_existsUnique R).1.exists

theorem wilsonLaw_isWilsonLaw (R : RootPair) : IsWilsonLaw R (wilsonLaw R) :=
  Classical.choose_spec (FiniteAvalanches.External.wilson_two_color_law_existsUnique R).1.exists

theorem wilsonLaw_unique (R : RootPair) {ν : ProbabilityMeasure ForestField}
    (h : IsWilsonLaw R ν) : ν = wilsonLaw R :=
  (FiniteAvalanches.External.wilson_two_color_law_existsUnique R).1.unique h (wilsonLaw_isWilsonLaw R)

theorem finiteForestProbability_tendsto (R : RootPair) :
    Filter.Tendsto (finiteForestProbability R) Filter.atTop (nhds (wilsonLaw R)) :=
  (FiniteAvalanches.External.wilson_two_color_law_existsUnique R).2 _ (wilsonLaw_isWilsonLaw R)

/-- The paper's actual nu_(A,C): the full color projection of the uniquely identified law. -/
def wilsonColorLaw (R : RootPair) : Measure ColorField :=
  (wilsonLaw R : Measure ForestField).map Prod.snd
instance wilsonColorLaw_probability (R : RootPair) : IsProbabilityMeasure (wilsonColorLaw R) :=
  (wilsonLaw R : Measure ForestField).isProbabilityMeasure_map measurable_snd.aemeasurable

/-- Genuine downstream finite-pattern law; unknown colors never satisfy a pattern. -/
theorem wilsonColorLaw_apply_sampler (R : RootPair) (L : List (Site 2)) (D : Finset (Site 2))
    (p : Site 2 → Bool) (hD : ∀ d ∈ D, d ∈ L) :
    wilsonColorLaw R {σ | ∀ d ∈ D, σ d = p d} =
      wilsonRows {ξ | ∃ st, samplerRun (initialSampler R) L ξ = some st ∧
        ∀ d ∈ D, st.colors d = some (p d)} := by
  have hm : MeasurableSet {σ : ColorField | ∀ d ∈ D, σ d = p d} := by
    have he : {σ : ColorField | ∀ d ∈ D, σ d = p d} = ⋂ d ∈ D, {σ | σ d = p d} := by
      ext σ; simp
    rw [he]
    exact Finset.measurableSet_biInter D (fun d _ =>
      (isClosed_eq (continuous_apply d : Continuous (fun σ : ColorField => σ d))
        continuous_const).measurableSet)
  rw [wilsonColorLaw, Measure.map_apply measurable_snd hm]
  have h := (wilsonLaw_isWilsonLaw R).2 L ∅ D (fun _ => false) p (by simp) hD
  simpa only [jointEvent, samplerEvent, Finset.notMem_empty, IsEmpty.forall_iff,
    implies_true, forall_const, true_and, Set.preimage_setOf_eq] using h

/-- Termination is DERIVED from the empty observation of the full joint law, not a premise. -/
theorem wilson_sampler_success_mass_one (R : RootPair) (L : List (Site 2)) :
    wilsonRows {ξ | ∃ st, samplerRun (initialSampler R) L ξ = some st} = 1 := by
  have h := (wilsonLaw_isWilsonLaw R).2 L ∅ ∅ (fun _ => false) (fun _ => true) (by simp) (by simp)
  simpa [jointEvent, samplerEvent] using h.symm

/-- Actual almost-everywhere success: open-event measurability is proved above,
so this is stronger than an unqualified outer-measure-one assertion. -/
theorem wilson_sampler_success_conull (R : RootPair) (L : List (Site 2)) :
    ∀ᵐ ξ ∂wilsonRows, ∃ st, samplerRun (initialSampler R) L ξ = some st :=
  (mem_ae_iff_prob_eq_one (measurableSet_sampler_success (initialSampler R) L)).mpr
    (wilson_sampler_success_mass_one R L)

/-- Every original root, not only the queried ones, has its source color. -/
theorem wilsonLaw_ae_root_colors (R : RootPair) :
    ∀ᵐ ω ∂(wilsonLaw R : Measure ForestField),
      (∀ x ∈ R.one, ω.2 x = true) ∧ ∀ x ∈ R.zero, ω.2 x = false := by
  filter_upwards [(wilsonLaw_isWilsonLaw R).1] with ω hω
  have hc : ω.2 = colors R ⟨ω.1, hω.1⟩ := (colored_iff_colors R ⟨ω.1, hω.1⟩ ω.2).mp hω
  exact ⟨fun x hx => by rw [hc]; exact colors_of_one_root R _ hx,
    fun x hx => by rw [hc]; exact colors_of_zero_root R _ hx⟩

end
end FiniteAvalanches.Wilson.Lattice
