import FiniteAvalanches.Wilson.Kernel
import FiniteAvalanches.Wilson.ClassicalProtocol
import Mathlib.Logic.Equiv.Prod

/-! Independent uniform legal-letter vectors have the same incident-copy
marginals as ordinary unit-copy walks. This is a comparison of observed walk
laws, not an equality with correlated full-letter realizations. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open scoped Classical ENNReal
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E) [Nontrivial V]
variable (hconn : ∀ x y, G.reaches Finset.univ x y)
variable [∀ v : V, MeasurableSpace (Incident G v)] [∀ v : V, MeasurableSingletonClass (Incident G v)]

instance uniformLetterLaw_probability : IsProbabilityMeasure (uniformLetterLaw G hconn) := by
  unfold uniformLetterLaw
  infer_instance

theorem uniformLetterLaw_eval (v : V) :
    (uniformLetterLaw G hconn).map (fun a => a v) = (unitCopyPMF G hconn v).toMeasure := by
  letI (w : V) : Nonempty (Incident G w) := incident_nonempty G hconn w
  apply Measure.ext_of_singleton
  intro e
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton e)]
  let Rest := (w : {w : V // w ≠ v}) → Incident G w.val
  let split : Letter G ≃ Incident G v × Rest := Equiv.piSplitAt v (Incident G)
  let fiber : {a : Letter G // a v = e} ≃ Rest :=
    { toFun := fun a w => a.val w.val
      invFun := fun f => ⟨split.symm (e, f), congrArg Prod.fst (split.apply_symm_apply (e, f))⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply split.injective
        rw [split.apply_symm_apply]
        apply Prod.ext
        · exact a.property.symm
        · rfl
      right_inv := by
        intro f
        have he := congrArg Prod.snd (split.apply_symm_apply (e, f))
        exact he }
  have hf : Fintype.card {a : Letter G // a v = e} = Fintype.card Rest := Fintype.card_congr fiber
  have hc : Fintype.card (Letter G) = Fintype.card (Incident G v) * Fintype.card Rest := by
    rw [Fintype.card_congr split, Fintype.card_prod]
  have hr : (Fintype.card Rest : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Rest ≠ 0)
  change (PMF.uniformOfFintype (Letter G)).toMeasure {a | a v = e} = _
  rw [PMF.toMeasure_uniformOfFintype_apply {a : Letter G | a v = e} (show MeasurableSet {a : Letter G | a v = e} from trivial)]
  change (Fintype.card {a : Letter G // a v = e} : ℝ≥0∞) / Fintype.card (Letter G) = _
  rw [hf, hc]
  rw [(unitCopyPMF G hconn v).toMeasure_apply_singleton e (measurableSet_singleton e), unitCopyPMF_apply, Nat.cast_mul, div_eq_mul_inv, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  calc
    _ = (Fintype.card (Incident G v) : ℝ≥0∞)⁻¹ *
        ((Fintype.card Rest : ℝ≥0∞) * (Fintype.card Rest : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hr (ENNReal.natCast_ne_top _)]; exact mul_one _

variable {I : Type} [Countable I] (ι : E ↪ I)
variable (μ : Measure (Letter G)) [IsProbabilityMeasure μ]

/-- The whole history/output law is unchanged by the canonical uniform-letter realization. -/
theorem explorationLaw_eq_uniform_classical
    (hμ : ∀ v : V, μ.map (fun a => a v) = (unitCopyPMF G hconn v).toMeasure)
    (s : State (V := V) (E := E) (I := I)) (order : List V) :
    explorationLaw G ι μ s order =
      (driversLaw G (uniformLetterLaw G hconn)).map (classicalExplore G ι s order) := by
  letI : Nonempty (Letter G) := ⟨fun v => @Classical.ofNonempty _ (incident_nonempty G hconn v)⟩
  rw [explorationLaw_eq_of_incident_marginals G ι μ (uniformLetterLaw G hconn)
    (fun v => (hμ v).trans (uniformLetterLaw_eval G hconn v).symm)]
  exact explorationLaw_eq_classical G ι (uniformLetterLaw G hconn) s order

end
end FiniteAvalanches.Wilson.CopiedNetwork
