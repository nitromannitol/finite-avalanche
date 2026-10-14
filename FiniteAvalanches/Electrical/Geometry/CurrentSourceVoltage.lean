import FiniteAvalanches.Electrical.Geometry.SourceVoltage

/-! The historical constructor is a globally characterized harmonic extension
of explicit terminal boundary data. The source zero/one object is chosen only on
connected copied networks with distinct poles, from its proved unique spec. -/
namespace FiniteAvalanches.Electrical.Source.CurrentDomain
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- Full global meaning of the retained boundary-data constructor, including
coincident poles. No claim that both zero and one are prescribed at one vertex. -/
theorem voltage_boundary_data_spec (J : CopiedGraph V E) (alpha beta : V)
    (hc : (supportGraph J.left J.right).Preconnected) :
    (∀ x ∈ ({alpha, beta} : Finset V),
      voltage J alpha beta hc x = (if x = beta then 1 else 0)) ∧
    (∀ x, x ∉ ({alpha, beta} : Finset V) →
      laplacian J.left J.right (voltage J alpha beta hc) x = 0) := by
  exact harmonicExtension_spec J.left J.right {alpha,beta}
    (two_terminal_reachable J alpha beta hc) (fun x => if x = beta then (1 : ℝ) else 0)

/-- Every function with the complete boundary/harmonic data equals the retained
global constructor. This includes all public connected-network pole choices. -/
theorem voltage_boundary_data_unique (J : CopiedGraph V E) (alpha beta : V)
    (hc : (supportGraph J.left J.right).Preconnected) (f : V → ℝ)
    (hf : (∀ x ∈ ({alpha, beta} : Finset V), f x = (if x = beta then 1 else 0)) ∧
      ∀ x, x ∉ ({alpha, beta} : Finset V) → laplacian J.left J.right f x = 0) :
    f = voltage J alpha beta hc := by
  exact harmonicExtension_eq J.left J.right {alpha,beta}
    (two_terminal_reachable J alpha beta hc) (fun x => if x = beta then (1 : ℝ) else 0) f hf

def source_spec (J : CopiedGraph V E) (alpha beta : V) (f : V → ℝ) : Prop :=
  f alpha = 0 ∧ f beta = 1 ∧
    ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right f x = 0

/-- The exact source object exists uniquely on its full faithful public domain. -/
theorem existsUnique_source_voltage (J : CopiedGraph V E) (alpha beta : V)
    (hne : alpha ≠ beta) (hc : (supportGraph J.left J.right).Preconnected) :
    ∃! f : V → ℝ, source_spec J alpha beta f := by
  refine ⟨voltage J alpha beta hc, voltage_spec J alpha beta hne hc, ?_⟩
  intro f hf
  exact voltage_unique J alpha beta hne hc f hf.1 hf.2.1 hf.2.2

/-- Source-facing zero/one voltage: no equal-pole input or default value. -/
def source_voltage (J : CopiedGraph V E) (alpha beta : V)
    (hne : alpha ≠ beta) (hc : (supportGraph J.left J.right).Preconnected) : V → ℝ :=
  (existsUnique_source_voltage J alpha beta hne hc).choose

theorem source_voltage_spec (J : CopiedGraph V E) (alpha beta : V)
    (hne : alpha ≠ beta) (hc : (supportGraph J.left J.right).Preconnected) :
    source_spec J alpha beta (source_voltage J alpha beta hne hc) :=
  (existsUnique_source_voltage J alpha beta hne hc).choose_spec.1

theorem source_voltage_unique (J : CopiedGraph V E) (alpha beta : V)
    (hne : alpha ≠ beta) (hc : (supportGraph J.left J.right).Preconnected)
    (f : V → ℝ) (hf : source_spec J alpha beta f) :
    f = source_voltage J alpha beta hne hc :=
  (existsUnique_source_voltage J alpha beta hne hc).choose_spec.2 f hf

/-- Exact ordinary application bridge at every permitted BSST pole choice. -/
theorem source_voltage_eq_voltage (J : CopiedGraph V E) (alpha beta : V)
    (hne : alpha ≠ beta) (hc : (supportGraph J.left J.right).Preconnected) :
    source_voltage J alpha beta hne hc = voltage J alpha beta hc := by
  have hf := source_voltage_spec J alpha beta hne hc
  exact voltage_unique J alpha beta hne hc _ hf.1 hf.2.1 hf.2.2

theorem source_spec_iff_eq_source_voltage (J : CopiedGraph V E) (alpha beta : V)
    (hne : alpha ≠ beta) (hc : (supportGraph J.left J.right).Preconnected)
    (f : V → ℝ) :
    source_spec J alpha beta f ↔ f = source_voltage J alpha beta hne hc := by
  constructor
  · exact source_voltage_unique J alpha beta hne hc f
  · rintro rfl
    exact source_voltage_spec J alpha beta hne hc

end
end FiniteAvalanches.Electrical.Source.CurrentDomain

#print axioms FiniteAvalanches.Electrical.Source.CurrentDomain.voltage_boundary_data_spec
#print axioms FiniteAvalanches.Electrical.Source.CurrentDomain.voltage_boundary_data_unique
#print axioms FiniteAvalanches.Electrical.Source.CurrentDomain.existsUnique_source_voltage
#print axioms FiniteAvalanches.Electrical.Source.CurrentDomain.source_voltage_eq_voltage
#print axioms FiniteAvalanches.Electrical.Source.CurrentDomain.source_spec_iff_eq_source_voltage
