import FiniteAvalanches.Wilson.CopiedWalk
import Mathlib.Probability.Kernel.Basic

/-! Ordinary unit-copy transitions on a connected nontrivial finite network.
Conductance to an endpoint is the number of distinct incident copies. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open scoped Classical ENNReal
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E) [Nontrivial V]
variable (hconn : ∀ x y, G.reaches Finset.univ x y)

def unitCopyPMF (v : V) : PMF (Incident G v) := by
  letI := incident_nonempty G hconn v
  exact PMF.uniformOfFintype _

theorem unitCopyPMF_apply (v : V) (e : Incident G v) :
    unitCopyPMF G hconn v e = (Fintype.card (Incident G v) : ℝ≥0∞)⁻¹ := by
  letI := incident_nonempty G hconn v
  exact PMF.uniformOfFintype_apply e

def unitStepPMF (v : V) : PMF V := (unitCopyPMF G hconn v).map (other G v)

theorem unitStepPMF_apply (v w : V) :
    unitStepPMF G hconn v w =
      ((Finset.univ.filter (fun e : Incident G v => other G v e = w)).card : ℝ≥0∞) /
        Fintype.card (Incident G v) := by
  unfold unitStepPMF
  rw [PMF.map_apply, tsum_fintype]
  simp only [unitCopyPMF_apply]
  rw [← Finset.sum_filter]
  simp [eq_comm, div_eq_mul_inv]

variable [MeasurableSpace V] [MeasurableSingletonClass V]

def unitKernel : Kernel V V where
  toFun v := (unitStepPMF G hconn v).toMeasure
  measurable' := measurable_of_countable _

instance unitKernel_markov : IsMarkovKernel (unitKernel G hconn) where
  isProbabilityMeasure v := by change IsProbabilityMeasure (unitStepPMF G hconn v).toMeasure; infer_instance

end
end FiniteAvalanches.Wilson.CopiedNetwork
