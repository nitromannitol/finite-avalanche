import FiniteAvalanches.Trees.Lattice.WiredPastSitePattern

/-! The same original outgoing coordinate at an active finite vertex, including
an exit copy whose other original endpoint lies outside the wired box. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Trees.Lattice.CurrentWiredOutgoingRaw
open LatticeProb FiniteAvalanches.Sandpile TreeMeasurability11
open scoped Classical
noncomputable section

/-- The finite outgoing-copy clause is exactly an original edge to a site outside F.
The outside endpoint of an exit is retained; the sink never replaces that coordinate. -/
theorem outgoing_copy_iff_raw_outside (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) (a : FiniteWired.Active N)
    (e : FiniteWired.Edge N) :
    (((WiredTrees.graph N).left e = some a ∧
        (WiredTrees.graph N).right e ∉ activeLift N (F : Set (Site 2))) ∨
      ((WiredTrees.graph N).right e = some a ∧
        (WiredTrees.graph N).left e ∉ activeLift N (F : Set (Site 2)))) ↔
      ∃ y ∉ F, (originalCopyEdge e).val = s(FiniteWired.site a, y) := by
  cases e with
  | inl i =>
    change ((some i.val.1 = some a ∧ some i.val.2 ∉ activeLift N (F : Set (Site 2))) ∨
      (some i.val.2 = some a ∧ some i.val.1 ∉ activeLift N (F : Set (Site 2)))) ↔
      ∃ y ∉ F, s(FiniteWired.site i.val.1, FiniteWired.site i.val.2) = s(FiniteWired.site a, y)
    constructor
    · rintro (he | he)
      · have ha := Option.some.inj he.1
        subst a
        refine ⟨FiniteWired.site i.val.2, ?_, rfl⟩
        exact fun h => he.2 ((some_mem_activeLift N _ i.val.2).mpr h)
      · have ha := Option.some.inj he.1
        subst a
        refine ⟨FiniteWired.site i.val.1, ?_, Sym2.eq_swap⟩
        exact fun h => he.2 ((some_mem_activeLift N _ i.val.1).mpr h)
    · rintro ⟨y, hy, hp⟩
      rcases Sym2.eq_iff.mp hp with hp | hp
      · refine Or.inl ⟨congrArg some (FiniteWired.site_injective N hp.1), ?_⟩
        intro hv
        exact hy (hp.2 ▸ (some_mem_activeLift N _ i.val.2).mp hv)
      · refine Or.inr ⟨congrArg some (FiniteWired.site_injective N hp.2), ?_⟩
        intro hv
        exact hy (hp.1 ▸ (some_mem_activeLift N _ i.val.1).mp hv)
  | inr i =>
    change ((some i.val.1 = some a ∧ none ∉ activeLift N (F : Set (Site 2))) ∨
      (none = some a ∧ some i.val.1 ∉ activeLift N (F : Set (Site 2)))) ↔
      ∃ y ∉ F, s(FiniteWired.site i.val.1, FiniteWired.site i.val.1 + FiniteWired.step i.val.2) =
        s(FiniteWired.site a, y)
    constructor
    · rintro (he | he)
      · have ha := Option.some.inj he.1
        subst a
        refine ⟨FiniteWired.site i.val.1 + FiniteWired.step i.val.2, ?_, rfl⟩
        exact fun h => i.property (hbox _ h)
      · cases he.1
    · rintro ⟨y, _hy, hp⟩
      rcases Sym2.eq_iff.mp hp with hp | hp
      · exact Or.inl ⟨congrArg some (FiniteWired.site_injective N hp.1),
          sink_not_mem_activeLift N _⟩
      · exact False.elim (i.property (hp.2.symm ▸ fun j => (a j).property))


/-- The finite source union now has the literal original outgoing endpoint.
Both directions derive the same copied inside-tree and outgoing-coordinate witnesses. -/
theorem past_subset_iff_exists_raw_outgoing_pattern (N : ℕ)
    (t : (WiredTrees.graph N).SpanningTree) (x : Site 2)
    (hxbox : FiniteWired.inBox N x) (W : Finset (Site 2))
    (hWbox : ∀ y ∈ W, FiniteWired.inBox N y) :
    (WiredTrees.graph N).past t none
        (some (FiniteWired.activeOfSite N x hxbox)) (by simp) ⊆
      activeLift N (W : Set (Site 2)) ↔
    ∃ F : Finset (Site 2), F ⊆ W ∧ x ∈ F ∧ ∃ H : Finset (FiniteWired.Edge N),
      (WiredTrees.graph N).is_tree (activeLift N (F : Set (Site 2))) H ∧
      ∃ e : FiniteWired.Edge N,
        (∃ y ∉ F, (originalCopyEdge e).val = s(x, y)) ∧
        ∀ f ∈ incidentCoordinates F,
          CurrentOriginalField.originalWiredField t f =
            decide (f ∈ (insert e H).image originalCopyEdge) := by
  have hp := CurrentWiredPastSitePattern.past_subset_iff_exists_original_site_pattern
    N t x hxbox W hWbox
  have heq (F : Finset (Site 2)) (hFW : F ⊆ W) (e : FiniteWired.Edge N) :
      (((WiredTrees.graph N).left e = some (FiniteWired.activeOfSite N x hxbox) ∧
        (WiredTrees.graph N).right e ∉ activeLift N (F : Set (Site 2))) ∨
      ((WiredTrees.graph N).right e = some (FiniteWired.activeOfSite N x hxbox) ∧
        (WiredTrees.graph N).left e ∉ activeLift N (F : Set (Site 2)))) ↔
      ∃ y ∉ F, (originalCopyEdge e).val = s(x, y) := by
    exact outgoing_copy_iff_raw_outside N F (fun y hy => hWbox y (hFW hy))
      (FiniteWired.activeOfSite N x hxbox) e
  constructor
  · intro h
    obtain ⟨F, hFW, hxF, H, hH, e, he, hraw⟩ := hp.mp h
    exact ⟨F, hFW, hxF, H, hH, e, (heq F hFW e).mp he, hraw⟩
  · rintro ⟨F, hFW, hxF, H, hH, e, he, hraw⟩
    exact hp.mpr ⟨F, hFW, hxF, H, hH, e, (heq F hFW e).mpr he, hraw⟩

end
end FiniteAvalanches.Trees.Lattice.CurrentWiredOutgoingRaw

set_option pp.fullNames true
#print FiniteAvalanches.Trees.Lattice.CurrentWiredOutgoingRaw.outgoing_copy_iff_raw_outside
#print axioms FiniteAvalanches.Trees.Lattice.CurrentWiredOutgoingRaw.outgoing_copy_iff_raw_outside

#print FiniteAvalanches.Trees.Lattice.CurrentWiredOutgoingRaw.past_subset_iff_exists_raw_outgoing_pattern
#print axioms FiniteAvalanches.Trees.Lattice.CurrentWiredOutgoingRaw.past_subset_iff_exists_raw_outgoing_pattern
