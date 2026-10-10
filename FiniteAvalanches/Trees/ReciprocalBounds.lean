module

public import FiniteAvalanches.Trees.Reciprocal

@[expose] public section

/-! Nonroot ancestors have a real counted outgoing copy, so the reciprocal lies in [0,1]. -/
open scoped Classical
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Multigraph V E)

theorem admissibleEdges_nonempty_of_ancestor_ne_root (r : V) (S : Set V)
    (hS : S.Nonempty) (u : G.SpanningTree) (hne : G.ancestorOf u r S hS ≠ r) :
    (G.admissibleEdges (G.descendants u r (G.ancestorOf u r S hS)) (G.span u S)).Nonempty := by
  let a := G.ancestorOf u r S hS
  let p := G.ancestorCut r S hS ⟨u, hne⟩
  have he := G.parentEdge_spec u r a hne
  have hC : a ∈ G.descendants u r a := ancestor_refl _ r a
  have hK : a ∈ G.span u S := commonAncestor_mem_connectingSubtree _ r S hS
  have hc := p.property.2.2.1
  have hadm : G.admissible (G.descendants u r a) (G.span u S) p.val.2 := by
    rcases he.2 with hl | hr
    · have hl' : G.left p.val.2 = a := hl.1
      rcases hc with hc | hc
      · exact Or.inl ⟨⟨hl' ▸ hC, hl' ▸ hK⟩, hc.2⟩
      · exact (hc.1 (hl' ▸ hC)).elim
    · have hr' : G.right p.val.2 = a := hr.1
      rcases hc with hc | hc
      · exact (hc.2 (hr' ▸ hC)).elim
      · exact Or.inr ⟨⟨hr' ▸ hC, hr' ▸ hK⟩, hc.1⟩
  exact ⟨p.val.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadm⟩⟩

theorem reciprocalWeight_eq_inv_past (r : V) (S : Set V) (hS : S.Nonempty)
    (u : G.SpanningTree) (hne : G.ancestorOf u r S hS ≠ r) :
    G.reciprocalWeight r S hS 1 u =
      ((G.admissibleEdges (G.past u r (G.ancestorOf u r S hS) hne) (G.span u S)).card : ℝ)⁻¹ := by
  rw [G.past_eq_descendants]
  simp [reciprocalWeight, hne, one_div]

theorem reciprocalWeight_eq_zero_of_ancestor_eq_root (r : V) (S : Set V)
    (hS : S.Nonempty) (u : G.SpanningTree) (h : G.ancestorOf u r S hS = r) :
    G.reciprocalWeight r S hS 1 u = 0 := by simp [reciprocalWeight, h]

theorem reciprocalWeight_one_nonneg_le_one (r : V) (S : Set V) (hS : S.Nonempty)
    (u : G.SpanningTree) :
    0 ≤ G.reciprocalWeight r S hS 1 u ∧ G.reciprocalWeight r S hS 1 u ≤ 1 := by
  by_cases h : G.ancestorOf u r S hS ≠ r
  · rw [reciprocalWeight, if_pos h]
    have hc : (1 : ℝ) ≤
        (G.admissibleEdges (G.descendants u r (G.ancestorOf u r S hS)) (G.span u S)).card := by
      exact_mod_cast Finset.one_le_card.mpr (G.admissibleEdges_nonempty_of_ancestor_ne_root r S hS u h)
    constructor
    · positivity
    · apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hc)).mpr
      simpa using hc
  · simp [reciprocalWeight, h]

end FiniteAvalanches.Trees.Multigraph
