import FiniteAvalanches.Wilson.UniformLetters

/-! The canonical legal-letter realization drives the ordinary unit-copy
Markov kernel, including transitions at the chosen root. Stopping is separate. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory ProbabilityTheory MeasurableSpace FiniteAvalanches.Trees
open scoped Classical ENNReal
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E) [Nontrivial V]
variable (hconn : ∀ x y, G.reaches Finset.univ x y)
variable [MeasurableSpace V] [MeasurableSingletonClass V]
variable [∀ v : V, MeasurableSpace (Incident G v)] [∀ v : V, MeasurableSingletonClass (Incident G v)]

theorem uniform_letterKernel_eq_unitKernel : letterKernel G (uniformLetterLaw G hconn) = unitKernel G hconn := by
  ext v U
  have he : (uniformLetterLaw G hconn).map (fun a => other G v (a v)) =
      ((uniformLetterLaw G hconn).map (fun a => a v)).map (other G v) :=
    by
      have he := Measure.map_map (μ := uniformLetterLaw G hconn)
        (measurable_of_countable (other G v)) (measurable_of_countable (fun a : Letter G => a v))
      rw [show (other G v ∘ (fun a : Letter G => a v)) = (fun a => other G v (a v)) from rfl] at he
      exact he.symm
  change ((uniformLetterLaw G hconn).map (fun a => other G v (a v))) U = _
  rw [he, uniformLetterLaw_eval, PMF.toMeasure_map (other G v) (unitCopyPMF G hconn v) (measurable_of_countable _)]
  rfl

theorem uniform_transition_given_past (x : V) (n : ℕ) (H : Set (Driver G))
    (hH : MeasurableSet[pastSpace G n] H) (v : V) (U : Set V) :
    driverLaw G (uniformLetterLaw G hconn)
        {ω | ω ∈ H ∧ position G x ω n = v ∧ position G x ω (n + 1) ∈ U} =
      driverLaw G (uniformLetterLaw G hconn) {ω | ω ∈ H ∧ position G x ω n = v} *
        unitKernel G hconn v U := by
  rw [← uniform_letterKernel_eq_unitKernel G hconn]
  exact transition_given_past G (uniformLetterLaw G hconn) x n H hH v U

end
end FiniteAvalanches.Wilson.CopiedNetwork
