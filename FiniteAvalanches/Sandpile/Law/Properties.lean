import FiniteAvalanches.Sandpile.Law.FiniteVolume

namespace FiniteAvalanches.External.SandpileLimit

open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
  FiniteAvalanches.Probability
open scoped ENNReal Classical

noncomputable section

/-- Finite volumes exhausting `ℤ²`: every finite set is eventually contained. -/
def IsExhaustion (Λ : ℕ → Finset Site2) : Prop :=
  ∀ F : Finset Site2, ∀ᶠ n in atTop, F ⊆ Λ n

theorem isExhaustion_boxSites : IsExhaustion (fun n => boxSites n) := by
  intro F
  refine eventually_atTop.mpr ⟨F.sup (siteRadius 0), fun n hn x hx => ?_⟩
  exact (site_radius_zero_le_iff x n).mp ((Finset.le_sup (f := siteRadius 0) hx).trans hn)

/-- `μ` is the weak limit of the finite wired recurrent laws along every exhaustion. -/
def IsInfiniteVolumeLaw (μ : ProbabilityMeasure StableField) : Prop :=
  ∀ Λ : ℕ → Finset Site2, IsExhaustion Λ →
    Tendsto (fun n => finiteFieldProbabilityOn (Λ n)) atTop (nhds μ)

def IsTranslationInvariant (μ : ProbabilityMeasure StableField) : Prop :=
  ∀ z : Site2, (μ : Measure StableField).map (_root_.translate z) = (μ : Measure StableField)

end

end FiniteAvalanches.External.SandpileLimit
