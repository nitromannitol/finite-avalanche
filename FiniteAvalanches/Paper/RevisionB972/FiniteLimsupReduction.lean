import FiniteAvalanches.Sandpile.Source.ReciprocalReductionProvider
import FiniteAvalanches.Trees.Lattice.TreeContinuityProvider
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false
namespace FiniteAvalanches.Paper.RevisionB972
open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
open SourceCounting Components Trees.Lattice TreeMeasurability11 FiniteAvalanches.Sandpile.Source
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

/-- The source's finite-volume reciprocal is the actual all-copy wired-tree reciprocal
at every volume containing its complete marked set. -/
theorem finite_source_expectation_eq {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) =
      ∫ t, WiredTrees.reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t ∂WiredTrees.law N := by
  apply integral_congr_ae
  exact Eventually.of_forall fun t => (finite_reciprocal_eq_finiteZN hr hrN t).symm

/-- The finite-limsup radius reduction, with one universal constant preceding both scales. -/
theorem reciprocal_reduction_limsup :
    ∃ C : ℝ, ∀ r : ℕ, 2 ≤ r → ∀ M : ℕ, r + 2 ≤ M →
      (infiniteVolumeLaw : Measure StableField).real
          {η | ENNReal.ofReal (M : ℝ) < extendedCount (radius η 0)} ≤
        (Filter.limsup
          (fun N : ℕ => ∫ t, finiteZN N (sourceMarks r)
            (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) atTop) +
        C * (r : ℝ) * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C, hC⟩ := FiniteAvalanchesProofs.ReciprocalReduction.reciprocal_reduction
  refine ⟨C, ?_⟩
  intro r hr M hM
  have hlimit := JointTreeContinuity.tree_continuity.1
    (sourceMarks r) (Finset.insert_nonempty _ _)
  rw [hlimit.limsup_eq]
  simpa only [source_marks_eq_literal] using hC r hr M hM

end
end FiniteAvalanches.Paper.RevisionB972
