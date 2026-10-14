import FiniteAvalanches.Sandpile.Recurrence.RawGraphLaw

/-! Actual copied-edge walks and the support graph have the same connectivity. -/
namespace FiniteAvalanches.Paper.CurrentRawBurning
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E]
    (G : Multigraph V E)

/-- Each support adjacency has the same original E witness in either orientation. -/
theorem support_adj_iff (x y : V) :
    (FiniteAvalanches.Electrical.supportGraph G.left G.right).Adj x y ↔
      G.adjacent Finset.univ x y := by
  constructor
  · rintro ⟨_, e, he⟩
    exact ⟨e, Finset.mem_univ _, he⟩
  · rintro ⟨e, _, he⟩
    refine ⟨?_, e, he⟩
    intro hxy
    rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact G.loopless e (hl.trans (hxy.trans hr.symm))
    · exact G.loopless e (hl.trans (hxy.symm.trans hr.symm))

/-- The walk/relation dictionary includes zero-length paths and preserves endpoints. -/
theorem support_reachable_iff (x y : V) :
    (FiniteAvalanches.Electrical.supportGraph G.left G.right).Reachable x y ↔
      G.reaches Finset.univ x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have he : (FiniteAvalanches.Electrical.supportGraph G.left G.right).Adj =
      G.adjacent Finset.univ := by
    funext a b
    exact propext (support_adj_iff G a b)
  rw [he]
  rfl

theorem connected_iff_reaches : RawGraph.Connected G ↔
    ∀ x y : V, G.reaches Finset.univ x y := by
  constructor
  · intro hc x y
    exact (support_reachable_iff G x y).mp (hc x y)
  · intro hc x y
    exact (support_reachable_iff G x y).mpr (hc x y)

end
end FiniteAvalanches.Paper.CurrentRawBurning
