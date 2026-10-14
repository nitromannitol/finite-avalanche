import CurrentSource.RawFullRadius
import FiniteAvalanches.Sandpile.Recurrence.RawIntegerLaw
import FiniteAvalanches.Sandpile.Law.BoxLimit
import FiniteAvalanches.Sandpile.Law.Translation
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Instances.Int

/-! The source stationary law is the unique weak limit of actual raw accessible boxes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Sandpile.RawFull
open LatticeProb FiniteAvalanches Sandpile MeasureTheory Filter
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

instance sourceState_pseudoMetrizable : TopologicalSpace.PseudoMetrizableSpace SourceState := by
  letI : Encodable Site2 := Encodable.ofCountable Site2
  letI : PseudoEMetricSpace Field := PiCountable.pseudoEMetricSpace
  infer_instance

theorem continuous_nnEmbedding : Continuous nnEmbedding := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro x
  exact (continuous_of_discreteTopology : Continuous (fun a : Fin 4 => (a.val : ℤ))).comp
    (continuous_apply x)

theorem measurable_nnEmbedding : Measurable nnEmbedding := continuous_nnEmbedding.measurable

theorem measurableSet_nonnegative : MeasurableSet {η : SourceState | Nonnegative η} := by
  simp only [Nonnegative, Set.setOf_forall]
  exact MeasurableSet.iInter fun x => measurableSet_height_test x (fun a => 0 ≤ a)

/-- The prescribed raw finite-box field agrees with the integer input inside
the box and has zero exterior, using the proved unique recurrent encoding. -/
def boxEmbedding (N : ℕ) (η : RawInteger.RecurrentState N) : SourceState :=
  nnEmbedding (RawInteger.sourceEmbedding N η)

theorem boxEmbedding_inside {N : ℕ} (η : RawInteger.RecurrentState N)
    (x : FiniteWired.Active N) :
    (boxEmbedding N η).val (FiniteWired.site x) = η.val.val (RawInteger.boxVertex N x) :=
  RawInteger.source_embedding_value η x

theorem boxEmbedding_outside {N : ℕ} (η : RawInteger.RecurrentState N) (x : Site2)
    (hx : ¬FiniteWired.inBox N x) : (boxEmbedding N η).val x = 0 := by
  change ((FiniteWired.zeroExtend N (RawInteger.sourceRecurrentEquiv N η) x).val : ℤ) = 0
  rw [FiniteWired.zeroExtend_outside N _ x hx]
  rfl

theorem boxEmbedding_unique {N : ℕ} (η : RawInteger.RecurrentState N) (ζ : SourceState)
    (hi : ∀ x : FiniteWired.Active N,
      ζ.val (FiniteWired.site x) = η.val.val (RawInteger.boxVertex N x))
    (ho : ∀ x, ¬FiniteWired.inBox N x → ζ.val x = 0) : ζ = boxEmbedding N η := by
  apply Subtype.ext
  funext x
  by_cases hx : FiniteWired.inBox N x
  · exact (hi (FiniteWired.activeOfSite N x hx)).trans
      (boxEmbedding_inside η (FiniteWired.activeOfSite N x hx)).symm
  · exact (ho x hx).trans (boxEmbedding_outside η x hx).symm

instance integerRecurrentLaw_probability (N : ℕ) :
    IsProbabilityMeasure (RawInteger.integerRecurrentLaw N) := by
  change IsProbabilityMeasure (FiniteAvalanches.uniformMeasure (RawInteger.RecurrentState N))
  infer_instance

/-- Uniform law on all upper-stable integer targets accessible from every integer
input, embedded by the actual boxed source map. -/
def boxLaw (N : ℕ) : Measure SourceState :=
  (RawInteger.integerRecurrentLaw N).map (boxEmbedding N)

instance boxLaw_probability (N : ℕ) : IsProbabilityMeasure (boxLaw N) := by
  exact (RawInteger.integerRecurrentLaw N).isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

def boxProbability (N : ℕ) : ProbabilityMeasure SourceState := ⟨boxLaw N, inferInstance⟩

theorem boxLaw_eq_nn_map (N : ℕ) :
    boxLaw N = (FiniteWired.finiteFieldLaw N).map nnEmbedding := by
  rw [← RawInteger.integer_recurrent_law_embedding N,
    Measure.map_map measurable_nnEmbedding (measurable_of_finite _)]
  rfl

theorem boxProbability_eq_nn_map (N : ℕ) :
    boxProbability N = (Probability.finiteFieldProbability N).map measurable_nnEmbedding.aemeasurable := by
  apply Subtype.ext
  exact boxLaw_eq_nn_map N

theorem boxProbability_tendsto_nn_map :
    Tendsto boxProbability atTop
      (nhds (infiniteVolumeLaw.map measurable_nnEmbedding.aemeasurable)) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    Probability.finiteFieldProbability infiniteVolumeLaw
    tendsto_finiteFieldProbability_infiniteVolumeLaw continuous_nnEmbedding
  exact h.congr (fun N => (boxProbability_eq_nn_map N).symm)

theorem existsUnique_sourceLaw :
    ∃! μ : ProbabilityMeasure SourceState, Tendsto boxProbability atTop (nhds μ) := by
  refine ⟨infiniteVolumeLaw.map measurable_nnEmbedding.aemeasurable,
    boxProbability_tendsto_nn_map, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν boxProbability_tendsto_nn_map

/-- The source stationary state, chosen only after existence and uniqueness of
the weak limit of the actual raw accessible boxed laws have been proved. -/
def sourceLaw : ProbabilityMeasure SourceState :=
  Classical.choose existsUnique_sourceLaw.exists

theorem sourceLaw_tendsto : Tendsto boxProbability atTop (nhds sourceLaw) :=
  Classical.choose_spec existsUnique_sourceLaw.exists

theorem sourceLaw_unique (μ : ProbabilityMeasure SourceState)
    (hμ : Tendsto boxProbability atTop (nhds μ)) : μ = sourceLaw :=
  tendsto_nhds_unique hμ sourceLaw_tendsto

theorem sourceLaw_full_characterization (μ : ProbabilityMeasure SourceState) :
    μ = sourceLaw ↔ Tendsto boxProbability atTop (nhds μ) :=
  ⟨fun h => h ▸ sourceLaw_tendsto, sourceLaw_unique μ⟩

theorem sourceLaw_eq_nn_map : sourceLaw =
    infiniteVolumeLaw.map measurable_nnEmbedding.aemeasurable :=
  tendsto_nhds_unique sourceLaw_tendsto boxProbability_tendsto_nn_map

theorem sourceLaw_nonnegative_ae : ∀ᵐ η ∂(sourceLaw : Measure SourceState), Nonnegative η := by
  rw [sourceLaw_eq_nn_map]
  change ∀ᵐ η ∂((infiniteVolumeLaw : Measure Sandpile.StableField).map nnEmbedding), Nonnegative η
  apply (ae_map_iff measurable_nnEmbedding.aemeasurable measurableSet_nonnegative).mpr
  exact Eventually.of_forall fun _ _ => Nat.cast_nonneg _

def translate (z : Site2) (η : SourceState) : SourceState :=
  ⟨fun x => η.val (x - z), fun x => η.property (x - z)⟩

theorem continuous_translate (z : Site2) : Continuous (translate z) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x - z)).comp continuous_subtype_val

theorem translate_nnEmbedding (z : Site2) (η : Sandpile.StableField) :
    translate z (nnEmbedding η) = nnEmbedding (_root_.translate z η) := rfl

theorem sourceLaw_translationInvariant (z : Site2) :
    (sourceLaw : Measure SourceState).map (translate z) = (sourceLaw : Measure SourceState) := by
  rw [sourceLaw_eq_nn_map]
  change ((infiniteVolumeLaw : Measure Sandpile.StableField).map nnEmbedding).map (translate z) =
    (infiniteVolumeLaw : Measure Sandpile.StableField).map nnEmbedding
  have ht : Measurable (_root_.translate z : Sandpile.StableField → Sandpile.StableField) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply (x - z)
  rw [Measure.map_map (continuous_translate z).measurable measurable_nnEmbedding]
  have hcomp : (translate z ∘ nnEmbedding) = (nnEmbedding ∘ _root_.translate z) := rfl
  rw [hcomp, ← Measure.map_map measurable_nnEmbedding ht,
    isTranslationInvariant_infiniteVolumeLaw z]

/-- Equality of the whole source-law tail, for every real threshold, including
infinite radius; no event is restricted to a conveniently chosen slice. -/
theorem sourceLaw_real_radius_tail_eq (o : Site2) (R : ℝ) (hR : 0 ≤ R) :
    (sourceLaw : Measure SourceState).real
      {η | ENNReal.ofReal R < extendedCount (radius η o)} =
    (infiniteVolumeLaw : Measure Sandpile.StableField).real
      {η | ENNReal.ofReal R < extendedCount (FiniteAvalanches.radius η o)} := by
  apply congrArg ENNReal.toReal
  rw [sourceLaw_eq_nn_map]
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply measurable_nnEmbedding (measurableSet_real_radius_tail o R hR)]
  congr 1
  ext η
  change ENNReal.ofReal R < extendedCount (radius (nnEmbedding η) o) ↔
    ENNReal.ofReal R < extendedCount (FiniteAvalanches.radius η o)
  rw [radius_nn_eq]

/-- Stabilization is likewise transported on the entire actual source law. -/
theorem sourceLaw_stabilizes_ae_of_nn
    (h : ∀ᵐ η ∂(infiniteVolumeLaw : Measure Sandpile.StableField),
      FiniteAvalanches.FiniteStabilizable η (0 : Site2)) :
    ∀ᵐ η ∂(sourceLaw : Measure SourceState), FiniteStabilizable η (0 : Site2) := by
  rw [sourceLaw_eq_nn_map]
  change ∀ᵐ η ∂((infiniteVolumeLaw : Measure Sandpile.StableField).map nnEmbedding),
    FiniteStabilizable η (0 : Site2)
  apply (ae_map_iff measurable_nnEmbedding.aemeasurable (measurableSet_finiteStabilizable 0)).mpr
  exact h.mono fun η hη => (finiteStabilizable_nn_iff η 0).mpr hη

end
end FiniteAvalanches.Sandpile.RawFull

#print FiniteAvalanches.Sandpile.RawFull.sourceLaw
#print FiniteAvalanches.Sandpile.RawFull.sourceLaw_full_characterization
#print axioms FiniteAvalanches.Sandpile.RawFull.existsUnique_sourceLaw
#print axioms FiniteAvalanches.Sandpile.RawFull.sourceLaw_full_characterization
#print axioms FiniteAvalanches.Sandpile.RawFull.sourceLaw_nonnegative_ae
#print axioms FiniteAvalanches.Sandpile.RawFull.sourceLaw_translationInvariant
#print axioms FiniteAvalanches.Sandpile.RawFull.sourceLaw_real_radius_tail_eq
