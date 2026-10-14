import FiniteAvalanches.Paper.Current.Outflow
import FiniteAvalanches.Trees.Lattice.CurrentSourceReciprocal

/-! The current whole-fiber outflow bound consumes the source count on valid volumes. -/

namespace FiniteAvalanches.Paper.CurrentBurning
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components
open FiniteAvalanches.Sandpile.SourceCounting
open TreeMeasurability11 TreeMeasurability11.CurrentDomain MeasureTheory
open scoped Classical ENNReal
noncomputable section

theorem outflow_le_guarded_source_reciprocal {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) :
    (Nat.card {g : Punctured N (origin N) //
      sourceMarks r ⊆ core g.val ∧ ¬sourceMarks r ⊆ core (forward g).val} : ℝ) ≤
      (WiredTrees.treeCount N : ℝ) *
        ∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
          (fun _ hx => sourceMarks_inBox hr hrN hx) t ∂WiredTrees.law N := by
  have h := FiniteAvalanches.Paper.CurrentOutflow.outflow_card_le_treeCount_mul_reciprocal
    (activeMarks N r) (marked_neighborhood hr hrN)
  rw [markedSites_activeMarks hr hrN] at h
  have he :
      (fun t => WiredTrees.reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _
          (Marked.source_mem_of_marked_neighbors _ (marked_neighborhood hr hrN))) t) =
      (fun t => sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t) := by
    funext t
    exact (FiniteAvalanches.Sandpile.Source.finite_reciprocal_eq_finiteZN hr hrN t).trans
      (sourceFiniteReciprocal_eq_auxiliary N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t).symm
  rw [he] at h
  exact h

/-- No mark is lost at the endpoint volume. -/
theorem outflow_endpoint {r : ℕ} (hr : 2 ≤ r) :
    (Nat.card {g : Punctured r (origin r) //
      sourceMarks r ⊆ core g.val ∧ ¬sourceMarks r ⊆ core (forward g).val} : ℝ) ≤
      (WiredTrees.treeCount r : ℝ) *
        ∫ t, sourceFiniteReciprocal r (sourceMarks r) (Finset.insert_nonempty _ _)
          (fun _ hx => sourceMarks_inBox hr le_rfl hx) t ∂WiredTrees.law r :=
  outflow_le_guarded_source_reciprocal hr le_rfl

end
end FiniteAvalanches.Paper.CurrentBurning

#print axioms FiniteAvalanches.Paper.CurrentBurning.outflow_le_guarded_source_reciprocal
#print axioms FiniteAvalanches.Paper.CurrentBurning.outflow_endpoint
