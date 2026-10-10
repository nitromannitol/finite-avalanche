import FiniteAvalanches.Model.FiniteWired
import FiniteAvalanches.Sandpile.Measurability
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Dirac

/-! Finite height patterns determine a measure and a local limit, when it exists. -/
namespace FiniteAvalanches.Probability
open FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped ENNReal Classical
noncomputable section

/-- Finite-coordinate equality uses the literal height-field carrier. -/
theorem measure_eq_of_finite_patterns (μ ν : Measure StableField) [IsFiniteMeasure μ]
    (h : ∀ (F : Finset Site2) (p : F → Fin 4),
      μ {η | F.restrict η = p} = ν {η | F.restrict η = p}) : μ = ν := by
  have hm (F : Finset Site2) : Measure.map F.restrict μ = Measure.map F.restrict ν := by
    apply Measure.ext_of_singleton
    intro p
    have hf : Measurable (F.restrict : StableField → F → Fin 4) := measurable_pi_lambda _ (fun x => measurable_pi_apply x.val)
    rw [Measure.map_apply hf (measurableSet_singleton p),
      Measure.map_apply hf (measurableSet_singleton p)]
    exact h F p
  apply Measure.ext_of_generateFrom_of_iUnion
    (measurableCylinders (fun _ : Site2 => Fin 4)) (fun _ : ℕ => (Set.univ : Set StableField))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (Set.iUnion_const _) (fun _ => univ_mem_measurableCylinders _) (fun _ => measure_ne_top μ _)
  intro S hS
  obtain ⟨F, A, hA, rfl⟩ := (mem_measurableCylinders S).mp hS
  have hf : Measurable (F.restrict : StableField → F → Fin 4) := measurable_pi_lambda _ (fun x => measurable_pi_apply x.val)
  simpa only [Measure.map_apply hf hA, cylinder] using congrArg (fun m => m A) (hm F)

/-- The manuscript's full-field form of a finite pattern determines the same measure. -/
theorem measure_eq_of_field_cylinders (μ ν : Measure StableField) [IsFiniteMeasure μ]
    (h : ∀ (F : Finset Site2) (ζ : StableField),
      μ {η | ∀ x ∈ F, η x = ζ x} = ν {η | ∀ x ∈ F, η x = ζ x}) : μ = ν := by
  apply measure_eq_of_finite_patterns μ ν
  intro F p
  let ζ : StableField := fun x => if hx : x ∈ F then p ⟨x, hx⟩ else 0
  have he : {η : StableField | F.restrict η = p} = {η | ∀ x ∈ F, η x = ζ x} := by
    ext η
    constructor
    · intro hη x hx
      have hx' := congrFun hη ⟨x, hx⟩
      simpa only [Finset.restrict_def, ζ, dif_pos hx] using hx'
    · intro hη
      funext x
      simpa only [Finset.restrict_def, ζ, dif_pos x.property] using hη x.val x.property
  rw [he]
  exact h F ζ

/-- A limit of the literal finite recurrent counting laws is unique. -/
theorem local_limit_unique (μ ν : Measure StableField) [IsFiniteMeasure μ]
    (hμ : ∀ (F : Finset Site2) (ζ : StableField),
      Filter.Tendsto (fun N : ℕ =>
        FiniteWired.finiteFieldLaw N {η | ∀ x ∈ F, η x = ζ x})
        Filter.atTop (nhds (μ {η | ∀ x ∈ F, η x = ζ x})))
    (hν : ∀ (F : Finset Site2) (ζ : StableField),
      Filter.Tendsto (fun N : ℕ =>
        FiniteWired.finiteFieldLaw N {η | ∀ x ∈ F, η x = ζ x})
        Filter.atTop (nhds (ν {η | ∀ x ∈ F, η x = ζ x}))) : μ = ν := by
  apply measure_eq_of_field_cylinders μ ν
  intro F ζ
  exact tendsto_nhds_unique (hμ F ζ) (hν F ζ)

end
end FiniteAvalanches.Probability
