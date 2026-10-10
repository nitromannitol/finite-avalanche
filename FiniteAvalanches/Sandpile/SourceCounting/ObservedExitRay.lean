import FiniteAvalanches.Trees.Lattice.ObservedExitRayDictionary
import FiniteAvalanches.Sandpile.SourceCounting.ObservedSpanGeometry

/-! The six marked vertices give the connected finite observation and an
escaping ray in its actual one roots. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.Components
open FiniteAvalanches.Sandpile.SourceCounting FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

/-- The actual six-mark observation has all the geometry required for an
adjacent disjoint ray, with the final original exit copy still recorded. -/
theorem source_marks_observation_escaping_ray {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let Ksites := activeSites N ((graph N).span t S)
    let roots := observationRootPair N S hS t hne
    none ∉ (graph N).span t S ∧
    ((lattice 2).induce (Ksites : Set Site2)).Connected ∧
    sourceMarks r ⊆ Ksites ∧ (0 : Site2) ∈ Ksites ∧ axisSite r ∈ Ksites ∧
    r ≤ Ksites.sup (fun x => Ksites.sup (fun y => siteRadius x y)) ∧
    roots.zero = (Ksites : Set Site2) ∧
    ∃ (a : FiniteWired.Active N) (γ : SimpleRay),
      (graph N).ancestorOf t none S hS = some a ∧
      FiniteWired.site a ∈ Ksites ∧
      (lattice 2).Adj (FiniteWired.site a) (γ.vertex 0) ∧
      γ.vertices ⊆ roots.one ∧ Disjoint (Ksites : Set Site2) γ.vertices ∧
      ∃ e : FiniteWired.ExitEdge N,
        Sum.inr e ∈ (graph N).rootPathCopies t (some a) none ∧
        ∃ m : ℕ, ∀ n, γ.vertex (m + n) = FiniteExitRay.outwardVertex e.val.1 e.val.2 (n + 1) := by
  obtain ⟨hsink, hconnected, _, hmarks, hzero, haxis, hdiam, hroots⟩ :=
    source_marks_observed_span_geometry hr hrN t hne
  exact ⟨hsink, hconnected, hmarks, hzero, haxis, hdiam, hroots,
    observationRootPair_escaping_ray t _ _ hne⟩

end
end FiniteAvalanches.ConditioningConsumer
