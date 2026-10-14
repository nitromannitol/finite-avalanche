import CurrentSource.FullIntegerRadius
import CurrentSource.RawSourceLaw

/-! The prescribed stationary law on the entire product of integer coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Sandpile.FullInteger
open LatticeProb FiniteAvalanches Sandpile MeasureTheory Filter
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

instance field_pseudoMetrizable : TopologicalSpace.PseudoMetrizableSpace Field := by
  letI : Encodable Site2 := Encodable.ofCountable Site2
  letI : PseudoEMetricSpace Field := PiCountable.pseudoEMetricSpace
  infer_instance

theorem continuous_stableCoe : Continuous (Subtype.val : RawFull.SourceState → Field) :=
  continuous_subtype_val

theorem measurable_stableCoe : Measurable (Subtype.val : RawFull.SourceState → Field) :=
  continuous_stableCoe.measurable

/-- Literal integer coordinates, with no invalid-coordinate alternative. -/
def nnEmbedding (η : Sandpile.StableField) : Field := (RawFull.nnEmbedding η).val

theorem nnEmbedding_coordinates (η : Sandpile.StableField) (x : Site2) :
    nnEmbedding η x = ((η x).val : ℤ) := rfl

theorem continuous_nnEmbedding : Continuous nnEmbedding :=
  continuous_stableCoe.comp RawFull.continuous_nnEmbedding

theorem measurable_nnEmbedding : Measurable nnEmbedding := continuous_nnEmbedding.measurable

/-- The actual raw accessible boxed sandpile, with its prescribed zero exterior. -/
def boxEmbedding (N : ℕ) (η : RawInteger.RecurrentState N) : Field :=
  (RawFull.boxEmbedding N η).val

theorem boxEmbedding_inside {N : ℕ} (η : RawInteger.RecurrentState N)
    (x : FiniteWired.Active N) :
    boxEmbedding N η (FiniteWired.site x) = η.val.val (RawInteger.boxVertex N x) :=
  RawFull.boxEmbedding_inside η x

theorem boxEmbedding_outside {N : ℕ} (η : RawInteger.RecurrentState N) (x : Site2)
    (hx : ¬FiniteWired.inBox N x) : boxEmbedding N η x = 0 :=
  RawFull.boxEmbedding_outside η x hx

/-- Uniqueness covers all integer fields, including initially unstable ones. -/
theorem boxEmbedding_unique {N : ℕ} (η : RawInteger.RecurrentState N) (ζ : Field)
    (hi : ∀ x : FiniteWired.Active N,
      ζ (FiniteWired.site x) = η.val.val (RawInteger.boxVertex N x))
    (ho : ∀ x, ¬FiniteWired.inBox N x → ζ x = 0) : ζ = boxEmbedding N η := by
  funext x
  by_cases hx : FiniteWired.inBox N x
  · exact (hi (FiniteWired.activeOfSite N x hx)).trans
      (boxEmbedding_inside η (FiniteWired.activeOfSite N x hx)).symm
  · exact (ho x hx).trans (boxEmbedding_outside η x hx).symm

theorem boxEmbedding_full_characterization {N : ℕ} (η : RawInteger.RecurrentState N)
    (ζ : Field) : ζ = boxEmbedding N η ↔
      (∀ x : FiniteWired.Active N,
        ζ (FiniteWired.site x) = η.val.val (RawInteger.boxVertex N x)) ∧
      (∀ x, ¬FiniteWired.inBox N x → ζ x = 0) := by
  constructor
  · rintro rfl
    exact ⟨boxEmbedding_inside η, boxEmbedding_outside η⟩
  · rintro ⟨hi, ho⟩
    exact boxEmbedding_unique η ζ hi ho

theorem existsUnique_boxEmbedding {N : ℕ} (η : RawInteger.RecurrentState N) :
    ∃! ζ : Field,
      (∀ x : FiniteWired.Active N,
        ζ (FiniteWired.site x) = η.val.val (RawInteger.boxVertex N x)) ∧
      (∀ x, ¬FiniteWired.inBox N x → ζ x = 0) :=
  ⟨boxEmbedding N η, ⟨boxEmbedding_inside η, boxEmbedding_outside η⟩,
    fun ζ h => boxEmbedding_unique η ζ h.1 h.2⟩

def boxLaw (N : ℕ) : Measure Field :=
  (RawInteger.integerRecurrentLaw N).map (boxEmbedding N)

instance boxLaw_probability (N : ℕ) : IsProbabilityMeasure (boxLaw N) :=
  (RawInteger.integerRecurrentLaw N).isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

def boxProbability (N : ℕ) : ProbabilityMeasure Field := ⟨boxLaw N, inferInstance⟩

theorem boxLaw_eq_stable_map (N : ℕ) :
    boxLaw N = (RawFull.boxLaw N).map (Subtype.val : RawFull.SourceState → Field) := by
  rw [RawFull.boxLaw, Measure.map_map measurable_stableCoe (measurable_of_finite _)]
  rfl

theorem boxProbability_eq_stable_map (N : ℕ) :
    boxProbability N = (RawFull.boxProbability N).map measurable_stableCoe.aemeasurable := by
  apply Subtype.ext
  exact boxLaw_eq_stable_map N

/-- Existence is derived from the characterized stable auxiliary via continuous
inclusion; the resulting uniqueness quantifies over every probability on Field. -/
theorem boxProbability_tendsto_stable_map :
    Tendsto boxProbability atTop
      (nhds (RawFull.sourceLaw.map measurable_stableCoe.aemeasurable)) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    RawFull.boxProbability RawFull.sourceLaw RawFull.sourceLaw_tendsto continuous_stableCoe
  exact h.congr (fun N => (boxProbability_eq_stable_map N).symm)

theorem existsUnique_sourceLaw :
    ∃! μ : ProbabilityMeasure Field, Tendsto boxProbability atTop (nhds μ) := by
  refine ⟨RawFull.sourceLaw.map measurable_stableCoe.aemeasurable,
    boxProbability_tendsto_stable_map, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν boxProbability_tendsto_stable_map

/-- The source measure is chosen only after full-carrier weak-limit uniqueness. -/
def sourceLaw : ProbabilityMeasure Field := Classical.choose existsUnique_sourceLaw.exists

theorem sourceLaw_tendsto : Tendsto boxProbability atTop (nhds sourceLaw) :=
  Classical.choose_spec existsUnique_sourceLaw.exists

theorem sourceLaw_unique (μ : ProbabilityMeasure Field)
    (hμ : Tendsto boxProbability atTop (nhds μ)) : μ = sourceLaw :=
  tendsto_nhds_unique hμ sourceLaw_tendsto

theorem sourceLaw_full_characterization (μ : ProbabilityMeasure Field) :
    μ = sourceLaw ↔ Tendsto boxProbability atTop (nhds μ) :=
  ⟨fun h => h ▸ sourceLaw_tendsto, sourceLaw_unique μ⟩

theorem sourceLaw_eq_stable_map :
    sourceLaw = RawFull.sourceLaw.map measurable_stableCoe.aemeasurable :=
  tendsto_nhds_unique sourceLaw_tendsto boxProbability_tendsto_stable_map

theorem sourceLaw_eq_nn_map : sourceLaw =
    infiniteVolumeLaw.map measurable_nnEmbedding.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [sourceLaw_eq_stable_map, RawFull.sourceLaw_eq_nn_map]
  change ((infiniteVolumeLaw : Measure Sandpile.StableField).map RawFull.nnEmbedding).map
      (Subtype.val : RawFull.SourceState → Field) =
    (infiniteVolumeLaw : Measure Sandpile.StableField).map nnEmbedding
  rw [Measure.map_map measurable_stableCoe RawFull.measurable_nnEmbedding]
  rfl

def Nonnegative (η : Field) : Prop := ∀ x, 0 ≤ η x
def UpperStable (η : Field) : Prop := ∀ x, η x < 4

theorem measurableSet_nonnegative : MeasurableSet {η : Field | Nonnegative η} := by
  simp only [Nonnegative, Set.setOf_forall]
  exact MeasurableSet.iInter fun x => measurableSet_height_test x (fun a => 0 ≤ a)

theorem measurableSet_upperStable : MeasurableSet {η : Field | UpperStable η} := by
  simp only [UpperStable, Set.setOf_forall]
  exact MeasurableSet.iInter fun x => measurableSet_height_test x (fun a => a < 4)

theorem sourceLaw_nonnegative_ae : ∀ᵐ η ∂(sourceLaw : Measure Field), Nonnegative η := by
  rw [sourceLaw_eq_nn_map]
  change ∀ᵐ η ∂((infiniteVolumeLaw : Measure Sandpile.StableField).map nnEmbedding), Nonnegative η
  apply (ae_map_iff measurable_nnEmbedding.aemeasurable measurableSet_nonnegative).mpr
  exact Eventually.of_forall fun _ _ => Nat.cast_nonneg _

theorem sourceLaw_upperStable_ae : ∀ᵐ η ∂(sourceLaw : Measure Field), UpperStable η := by
  rw [sourceLaw_eq_nn_map]
  change ∀ᵐ η ∂((infiniteVolumeLaw : Measure Sandpile.StableField).map nnEmbedding), UpperStable η
  apply (ae_map_iff measurable_nnEmbedding.aemeasurable measurableSet_upperStable).mpr
  exact Eventually.of_forall fun η x => (RawFull.nnEmbedding η).property x

def translate (z : Site2) (η : Field) : Field := fun x => η (x - z)

theorem continuous_translate (z : Site2) : Continuous (translate z) :=
  continuous_pi fun x => continuous_apply (x - z)

theorem translate_nnEmbedding (z : Site2) (η : Sandpile.StableField) :
    translate z (nnEmbedding η) = nnEmbedding (_root_.translate z η) := rfl

theorem sourceLaw_translationInvariant (z : Site2) :
    (sourceLaw : Measure Field).map (translate z) = (sourceLaw : Measure Field) := by
  rw [sourceLaw_eq_nn_map]
  change ((infiniteVolumeLaw : Measure Sandpile.StableField).map nnEmbedding).map (translate z) =
    (infiniteVolumeLaw : Measure Sandpile.StableField).map nnEmbedding
  have ht : Measurable (_root_.translate z : Sandpile.StableField → Sandpile.StableField) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply (x - z)
  rw [Measure.map_map (continuous_translate z).measurable measurable_nnEmbedding]
  have hcomp : (translate z ∘ nnEmbedding) = (nnEmbedding ∘ _root_.translate z) := rfl
  rw [hcomp, ← Measure.map_map measurable_nnEmbedding ht,
    isTranslationInvariant_infiniteVolumeLaw z]

/-- The event is on the entire Field carrier; agreement with NN uses the proved
stable restriction, not an artificial definition outside the support. -/
theorem sourceLaw_real_radius_tail_eq (o : Site2) (R : ℝ) (hR : 0 ≤ R) :
    (sourceLaw : Measure Field).real
      {η | ENNReal.ofReal R < extendedCount (radius η o)} =
    (infiniteVolumeLaw : Measure Sandpile.StableField).real
      {η | ENNReal.ofReal R < extendedCount (FiniteAvalanches.radius η o)} := by
  apply congrArg ENNReal.toReal
  rw [sourceLaw_eq_nn_map, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply measurable_nnEmbedding (measurableSet_real_radius_tail o R hR)]
  congr 1
  ext η
  change ENNReal.ofReal R < extendedCount (radius (RawFull.nnEmbedding η).val o) ↔
    ENNReal.ofReal R < extendedCount (FiniteAvalanches.radius η o)
  rw [radius_nn_eq]

theorem sourceLaw_stabilizes_ae_of_nn
    (h : ∀ᵐ η ∂(infiniteVolumeLaw : Measure Sandpile.StableField),
      FiniteAvalanches.FiniteStabilizable η (0 : Site2)) :
    ∀ᵐ η ∂(sourceLaw : Measure Field), FiniteStabilizable η (0 : Site2) := by
  rw [sourceLaw_eq_nn_map]
  change ∀ᵐ η ∂((infiniteVolumeLaw : Measure Sandpile.StableField).map nnEmbedding),
    FiniteStabilizable η (0 : Site2)
  apply (ae_map_iff measurable_nnEmbedding.aemeasurable (measurableSet_finiteStabilizable 0)).mpr
  exact h.mono fun η hη => (finiteStabilizable_stable_iff (RawFull.nnEmbedding η) 0).mpr
    ((RawFull.finiteStabilizable_nn_iff η 0).mpr hη)

end
end FiniteAvalanches.Sandpile.FullInteger
