import FiniteAvalanches.Sandpile.SourceCounting.CountingGeometry

namespace FiniteAvalanches.Sandpile.SourceCounting
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

/-- The horizontal path alone connects zero to every one of its prefixes. -/
theorem horizontalPath_reaches {N r : ℕ} (hrN : r ≤ N) (k : ℕ) (hk : k ≤ r) :
    (WiredTrees.graph N).reaches (horizontalPath N r hrN)
      (some (origin N)) (some (axisVertex N k (hk.trans hrN))) := by
  induction k with
  | zero => rw [axisVertex_zero]; exact .refl
  | succ k ih =>
    have hm : horizontalEdge N r hrN ⟨k, by omega⟩ ∈ horizontalPath N r hrN :=
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    have hstep : (WiredTrees.graph N).adjacent (horizontalPath N r hrN)
        (some (axisVertex N k (by omega))) (some (axisVertex N (k+1) (hk.trans hrN))) :=
      ⟨horizontalEdge N r hrN ⟨k, by omega⟩, hm, Or.inl ⟨rfl, rfl⟩⟩
    exact (ih (by omega)).trans (Relation.ReflTransGen.single hstep)

theorem positive_singleton_reaches {N : ℕ} (hN : 1 ≤ N) (i : Fin 2) :
    (WiredTrees.graph N).reaches {FiniteWired.directionEdge (origin N) (i, true)}
      (some (origin N)) (some (FiniteWired.activeOfSite N (unit i) (unit_inBox hN i))) := by
  apply Relation.ReflTransGen.single
  refine ⟨_, Finset.mem_singleton_self _, Or.inl ⟨?_, ?_⟩⟩
  · change (FiniteWired.endpoints _).1 = _
    rw [positive_endpoints hN i]
  · change (FiniteWired.endpoints _).2 = _
    rw [positive_endpoints hN i]

theorem negative_singleton_reaches {N : ℕ} (hN : 1 ≤ N) (i : Fin 2) :
    (WiredTrees.graph N).reaches {FiniteWired.directionEdge (origin N) (i, false)}
      (some (origin N)) (some (FiniteWired.activeOfSite N (-unit i) (neg_unit_inBox hN i))) := by
  apply Relation.ReflTransGen.single
  refine ⟨_, Finset.mem_singleton_self _, Or.inr ⟨?_, ?_⟩⟩
  · change (FiniteWired.endpoints _).2 = _
    rw [negative_endpoints hN i]
  · change (FiniteWired.endpoints _).1 = _
    rw [negative_endpoints hN i]

/-- Each mark has its literal empty, singleton, or horizontal path inside `F_r`. -/
theorem fixed_paths_cover_marks {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    (y : FiniteWired.Active N) (hy : y ∈ activeMarks N r) :
    ∃ P : Finset (FiniteWired.Edge N), P ⊆ sourceEdges N r hrN ∧
      (WiredTrees.graph N).reaches P (some (origin N)) (some y) := by
  have hm := (Finset.mem_filter.mp hy).2
  rcases Finset.mem_insert.mp hm with hm | hm
  · have he : y = axisVertex N r hrN := FiniteWired.site_injective N hm
    refine ⟨horizontalPath N r hrN, Finset.subset_union_left, ?_⟩
    rw [he]
    exact horizontalPath_reaches hrN r le_rfl
  · rcases Finset.mem_insert.mp hm with hm | hm
    · have he : y = origin N := FiniteWired.site_injective N hm
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      rw [he]
      exact .refl
    · obtain ⟨i, hi | hi⟩ := (FiniteWired.mem_neighbors_iff 0 (FiniteWired.site y)).mp hm
      · have he : y = FiniteWired.activeOfSite N (unit i) (unit_inBox (by omega) i) := by
          apply FiniteWired.site_injective N
          simpa only [zero_add, FiniteWired.site_activeOfSite] using hi
        refine ⟨{FiniteWired.directionEdge (origin N) (i, true)},
          Finset.singleton_subset_iff.mpr (directionEdge_mem_sourceEdges hr hrN _), ?_⟩
        rw [he]
        exact positive_singleton_reaches (by omega) i
      · have hs : FiniteWired.site y = -unit i := by
          have h := congrArg (fun z : Site2 => z - unit i) hi
          simpa using h.symm
        have he : y = FiniteWired.activeOfSite N (-unit i) (neg_unit_inBox (by omega) i) :=
          FiniteWired.site_injective N hs
        refine ⟨{FiniteWired.directionEdge (origin N) (i, false)},
          Finset.singleton_subset_iff.mpr (directionEdge_mem_sourceEdges hr hrN _), ?_⟩
        rw [he]
        exact negative_singleton_reaches (by omega) i

end
end FiniteAvalanches.Sandpile.SourceCounting
