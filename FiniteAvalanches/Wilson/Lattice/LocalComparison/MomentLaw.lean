import FiniteAvalanches.Wilson.Lattice.LocalComparison.BoxSourceLawComparison
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ZeroExteriorLaw
import FiniteAvalanches.Wilson.Lattice.ReciprocalContactMonotonicity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
namespace LocalMomentLaw
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.Plane.SourceLattice MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

/-- The source H0 boundary observable on color fields: all exterior incidences, less the marked copy. -/
def sourceY (D : Finset (Site 2)) (σ : ColorField) : ℝ :=
  (contacts (LocalBoxContraction.exteriorSites D) σ : ℝ) - 1

theorem measurable_sourceY (D : Finset (Site 2)) : Measurable (sourceY D) :=
  ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (continuous_contacts _).measurable).sub measurable_const

theorem sourceY_reference (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : LocalBoxContraction.ReferenceForest D P marked) :
    sourceY D (LocalBoxContraction.referenceField D P marked F) =
      ReferenceMoment.boundaryContacts D P marked F := by
  rw [LocalBoxContraction.marked_boundary_subtract_one,
    LocalBoxContraction.originalBoundary_rawCount,
    LocalBoxContraction.rawBoundaryCount_contacts D _
      (LocalBoxContraction.reference_field_exterior D P marked F)]
  rfl

theorem reference_nonneg (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : LocalBoxContraction.ReferenceForest D P marked) :
    0 ≤ ReferenceMoment.boundaryContacts D P marked F := by
  apply Finset.sum_nonneg
  intro z _
  split_ifs <;> norm_num

theorem integrable_finite {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) :
    Integrable X μ := by
  apply (integrable_const (∑ x, ‖X x‖)).mono' (measurable_of_finite X).aestronglyMeasurable
  exact ae_of_all μ (fun x => Finset.single_le_sum (fun y _ => norm_nonneg (X y)) (Finset.mem_univ x))

/-- Every color field in the image of the entire forest carrier has positive mass,
and no field outside that image has positive mass. -/
theorem actual_full_support (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (marked : MarkedCopy D P) (σ : ColorField) :
    0 < wilsonColorLaw (LocalZeroExterior.domainRoots D P) {σ} ↔
      σ ∈ Set.range (LocalBoxContraction.referenceField D P marked) := by
  letI : Nonempty (LocalBoxContraction.ReferenceForest D P marked) :=
    LocalBoxContraction.referenceForest_nonempty D P N hDbox marked
  rw [← LocalBoxContraction.reference_color_law D P N hDbox marked,
    Measure.map_apply (measurable_of_finite _) (measurableSet_singleton σ),
    uniformMeasure_apply, ENNReal.div_pos_iff]
  constructor
  · intro h
    have hp : 0 < (Nat.card (LocalBoxContraction.referenceField D P marked ⁻¹' {σ}) : ℝ≥0∞) :=
      pos_iff_ne_zero.mpr h.1
    have hn : 0 < Nat.card (LocalBoxContraction.referenceField D P marked ⁻¹' {σ}) := by
      exact_mod_cast hp
    obtain ⟨f⟩ := (Nat.card_pos_iff.mp hn).1
    exact ⟨f.val, Set.mem_singleton_iff.mp f.property⟩
  · rintro ⟨f,hf⟩
    letI : Nonempty (LocalBoxContraction.referenceField D P marked ⁻¹' {σ}) :=
      ⟨⟨f, Set.mem_singleton_iff.mpr hf⟩⟩
    constructor
    · apply ne_of_gt
      exact_mod_cast (Nat.card_pos : 0 < Nat.card (LocalBoxContraction.referenceField D P marked ⁻¹' {σ}))
    · exact ENNReal.natCast_ne_top _

/-- The entire finite forest carrier supplies support, nonnegativity, both integrable moments,
and the original full-denominator moment formulas under the actual Wilson color law. -/
theorem actual_law_moments (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (marked : MarkedCopy D P) :
    letI : Nonempty (LocalBoxContraction.ReferenceForest D P marked) :=
      LocalBoxContraction.referenceForest_nonempty D P N hDbox marked
    let μ := wilsonColorLaw (LocalZeroExterior.domainRoots D P)
    let F := LocalBoxContraction.ReferenceForest D P marked
    let Y := ReferenceMoment.boundaryContacts D P marked
    (Set.range (LocalBoxContraction.referenceField D P marked)).Finite ∧
    (∀ σ, 0 < μ {σ} ↔ σ ∈ Set.range (LocalBoxContraction.referenceField D P marked)) ∧
    (∀ᵐ σ ∂μ, σ ∈ Set.range (LocalBoxContraction.referenceField D P marked)) ∧
    (∀ᵐ σ ∂μ, (∀ x ∉ D, σ x = false) ∧ 0 ≤ sourceY D σ) ∧
    Integrable (sourceY D) μ ∧ Integrable (fun σ => (sourceY D σ)^2) μ ∧
    (∫ σ, sourceY D σ ∂μ) = (∑ f : F, Y f)/(Fintype.card F : ℝ) ∧
    (∫ σ, (sourceY D σ)^2 ∂μ) = (∑ f : F, (Y f)^2)/(Fintype.card F : ℝ) := by
  letI : Nonempty (LocalBoxContraction.ReferenceForest D P marked) :=
    LocalBoxContraction.referenceForest_nonempty D P N hDbox marked
  dsimp only
  have hlaw := LocalBoxContraction.reference_color_law D P N hDbox marked
  have hfield := measurable_of_finite (LocalBoxContraction.referenceField D P marked)
  have hs : (Set.range (LocalBoxContraction.referenceField D P marked)).Finite := Set.finite_range _
  have hrange : ∀ᵐ σ ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P),
      σ ∈ Set.range (LocalBoxContraction.referenceField D P marked) := by
    rw [← hlaw]
    exact ae_map_mem_range _ hs.measurableSet _
  refine ⟨hs, (fun σ => actual_full_support D P N hDbox marked σ), hrange, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hrange] with σ hσ
    obtain ⟨f,rfl⟩ := hσ
    exact ⟨LocalBoxContraction.reference_field_exterior D P marked f,
      (sourceY_reference D P marked f).symm ▸ reference_nonneg D P marked f⟩
  · rw [← hlaw]
    apply (integrable_map_measure (measurable_sourceY D).aestronglyMeasurable hfield.aemeasurable).mpr
    exact integrable_finite _ _
  · rw [← hlaw]
    apply (integrable_map_measure ((measurable_sourceY D).pow_const 2).aestronglyMeasurable hfield.aemeasurable).mpr
    exact integrable_finite _ _
  · rw [← hlaw, integral_map hfield.aemeasurable (measurable_sourceY D).aestronglyMeasurable,
      integral_uniformMeasure, Nat.card_eq_fintype_card]
    congr 1
    apply Finset.sum_congr rfl
    intro f _
    exact sourceY_reference D P marked f
  · rw [← hlaw, integral_map hfield.aemeasurable ((measurable_sourceY D).pow_const 2).aestronglyMeasurable,
      integral_uniformMeasure, Nat.card_eq_fintype_card]
    congr 1
    apply Finset.sum_congr rfl
    intro f _
    rw [sourceY_reference]

end
end LocalMomentLaw
