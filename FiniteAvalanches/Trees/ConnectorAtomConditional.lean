import FiniteAvalanches.Trees.ConnectorConditionalCount
import Mathlib.Probability.ConditionalProbability

namespace FiniteAvalanches.Trees.Multigraph

open MeasureTheory
open scoped Classical ENNReal
noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
variable [Nonempty G.SpanningTree]

/-- Conditioning on a populated connector atom gives the full rooted-forest
completion proportion for every event of original copied subsets. -/
theorem treeLaw_cond_connector_count_event (R : Set V) (H : Finset E)
    (hH : G.is_tree R H) (t₀ : G.SpanningTree) (hHt : H ⊆ t₀.val)
    (A : Set (Finset E)) :
    ProbabilityTheory.cond G.treeLaw {t | H ⊆ t.val}
        {t | H ⊆ t.val ∧ t.val \ H ∈ A} =
      (Nat.card {F : G.RootedForest R // F.val ∈ A} : ℝ≥0∞) /
        Nat.card (G.RootedForest R) := by
  have ha0 : G.treeLaw {t : G.SpanningTree | H ⊆ t.val} ≠ 0 :=
    (G.treeLaw_containing_connector_pos H t₀ hHt).ne'
  have haT : G.treeLaw {t : G.SpanningTree | H ⊆ t.val} ≠ ⊤ :=
    measure_ne_top _ _
  have hC : MeasurableSet {t : G.SpanningTree | H ⊆ t.val} :=
    (Set.toFinite _).measurableSet
  have hset : {t : G.SpanningTree | H ⊆ t.val} ∩
      {t : G.SpanningTree | H ⊆ t.val ∧ t.val \ H ∈ A} =
        {t : G.SpanningTree | H ⊆ t.val ∧ t.val \ H ∈ A} := by
    ext t
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  rw [ProbabilityTheory.cond_apply hC, hset,
    G.treeLaw_joint_containing_connector R H hH t₀ hHt A,
    ← mul_assoc, ENNReal.inv_mul_cancel ha0 haT, one_mul]

end
end FiniteAvalanches.Trees.Multigraph

set_option pp.universes true in
set_option pp.explicit true in
set_option pp.fullNames true in
#check @FiniteAvalanches.Trees.Multigraph.treeLaw_cond_connector_count_event
#print axioms FiniteAvalanches.Trees.Multigraph.treeLaw_cond_connector_count_event
