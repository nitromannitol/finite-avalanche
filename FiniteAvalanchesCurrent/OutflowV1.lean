import FiniteAvalanches.Paper.Current.RawPuncturedOutflow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanchesCurrent.Punctured
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Paper.RawPunctured
open FiniteAvalanches.Sandpile.Waves
open FiniteAvalanches.Sandpile.SourceCounting MeasureTheory
open TreeMeasurability11.CurrentDomain

/-- The source outflow count is bounded by the spanning-tree count times
the mean reciprocal of the original contact count. -/
theorem outflow {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    (Nat.card {η : State (origin N) // sourceMarks r ⊆ W η ∧
      ¬sourceMarks r ⊆ W (U η)} : ℝ) ≤
      (WiredTrees.treeCount N : ℝ) *
        ∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
          (fun _ hx => sourceMarks_inBox hr hrN hx) t ∂WiredTrees.law N := by
  exact FiniteAvalanches.Paper.RawPunctured.outflow hr hrN

end FiniteAvalanchesCurrent.Punctured
