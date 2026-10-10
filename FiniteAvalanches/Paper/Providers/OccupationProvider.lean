import FiniteAvalanches.Sandpile.Waves.Partition
import FiniteAvalanches.Sandpile.Components.Measure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace FiniteAvalanches.Sandpile.Waves.Source
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

/-- Finite occupation transport works in every additive commutative monoid. -/
theorem sum_excursions {M : Type*} [AddCommMonoid M] {N : ℕ}
    {o : FiniteWired.Active N} (q : Punctured N o → M) :
    (∑ h : TerminalState N o, ∑ j : Fin (returnTime h), q (inverse^[j.val] h.val)) =
      ∑ x : Punctured N o, q x := by
  calc
    _ = ∑ p : ExcursionPoint N o, q (excursionState p) :=
      (Fintype.sum_sigma (fun p : ExcursionPoint N o => q (excursionState p))).symm
    _ = _ := excursionEquiv.sum_comp q

instance terminalMeasurableSpace {N : ℕ} {o : FiniteWired.Active N} :
    MeasurableSpace (TerminalState N o) := ⊤

instance terminalMeasurableSingletonClass {N : ℕ} {o : FiniteWired.Active N} :
    MeasurableSingletonClass (TerminalState N o) := ⟨fun _ => trivial⟩

/-- Each excursion start has the mass of one original recurrent configuration. -/
def terminalCountingMeasure {N : ℕ} (o : FiniteWired.Active N) :
    Measure (TerminalState N o) :=
  (Fintype.card (FiniteWired.Recurrent N) : ℝ≥0∞)⁻¹ • Measure.count

theorem terminal_counting_singleton {N : ℕ} (o : FiniteWired.Active N)
    (h : TerminalState N o) (η : FiniteWired.Recurrent N) :
    terminalCountingMeasure o {h} = FiniteWired.law N {η} := by
  simp only [terminalCountingMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_singleton, mul_one, FiniteWired.law_singleton]

/-- The terminal measure is exactly the original punctured measure on its terminal subtype. -/
theorem terminal_counting_eq_comap {N : ℕ} (o : FiniteWired.Active N) :
    terminalCountingMeasure o = (puncturedCountingMeasure o).comap
      (Subtype.val : TerminalState N o → Punctured N o) := by
  apply Measure.ext_of_singleton
  intro h
  rw [Measure.comap_apply Subtype.val Subtype.val_injective
    (fun s _ => (s.toFinite.image Subtype.val).measurableSet) _
    (measurableSet_singleton h), Set.image_singleton]
  simp only [terminalCountingMeasure, punctured_counting_singleton,
    Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]

/-- Exact signed occupation with the original recurrent denominator. -/
theorem integral_excursions {N : ℕ} (o : FiniteWired.Active N)
    (q : Punctured N o → ℝ) :
    (∫ h, (∑ j : Fin (returnTime h), q (inverse^[j.val] h.val))
      ∂terminalCountingMeasure o) = ∫ x, q x ∂puncturedCountingMeasure o := by
  simp only [terminalCountingMeasure, puncturedCountingMeasure, integral_smul_measure,
    integral_count, sum_excursions]

/-- Nonnegative occupation includes infinite values without integrability premises. -/
theorem lintegral_excursions {N : ℕ} (o : FiniteWired.Active N)
    (q : Punctured N o → ℝ≥0∞) :
    (∫⁻ h, (∑ j : Fin (returnTime h), q (inverse^[j.val] h.val))
      ∂terminalCountingMeasure o) = ∫⁻ x, q x ∂puncturedCountingMeasure o := by
  simp only [terminalCountingMeasure, puncturedCountingMeasure, lintegral_smul_measure,
    lintegral_count, tsum_fintype, sum_excursions]

/-- Every cycle meets the terminal locus and its full excursions give exact occupation. -/
theorem exact_occupation {N : ℕ} (o : FiniteWired.Active N) :
    (∀ x : Punctured N o, ∃ j : ℕ, terminal (inverse^[j] x)) ∧
    Function.Bijective (@excursionState N o) ∧
    (∀ q : Punctured N o → ℝ,
      (∫ h, (∑ j : Fin (returnTime h), q (inverse^[j.val] h.val))
        ∂terminalCountingMeasure o) = ∫ x, q x ∂puncturedCountingMeasure o) ∧
    (∀ q : Punctured N o → ℝ≥0∞,
      (∫⁻ h, (∑ j : Fin (returnTime h), q (inverse^[j.val] h.val))
        ∂terminalCountingMeasure o) = ∫⁻ x, q x ∂puncturedCountingMeasure o) :=
  ⟨inverse_orbit_reaches_terminal, ⟨excursion_state_injective, excursion_state_surjective⟩,
    integral_excursions o, lintegral_excursions o⟩


theorem paper_exact_occupation {N : ℕ} (o : FiniteWired.Active N) :
    (∀ h : Punctured N o, ∃ j : ℕ, terminal (inverse^[j] h)) ∧
    (∀ q : Punctured N o → ℝ,
      (∫ h, (∑ j : Fin (returnTime h), q (inverse^[j.val] h.val))
        ∂FiniteAvalanches.Sandpile.Waves.Source.terminalCountingMeasure o) =
      ∫ h, q h ∂puncturedCountingMeasure o) := by
  have hfull := FiniteAvalanches.Sandpile.Waves.Source.exact_occupation o
  exact ⟨hfull.1, hfull.2.2.1⟩

end
end FiniteAvalanches.Sandpile.Waves.Source
