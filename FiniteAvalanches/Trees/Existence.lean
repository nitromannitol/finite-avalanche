import FiniteAvalanches.Trees.Ancestors
import Mathlib.Data.Finset.Max

/-! A connected finite copied graph has an actual spanning tree. -/
namespace FiniteAvalanches.Trees.Multigraph
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
  (G : FiniteAvalanches.Trees.Multigraph V E)

/-- Individual parallel edge copies are retained in the spanning-tree carrier. -/
theorem nonempty_spanning_tree [Nonempty V]
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) : Nonempty G.SpanningTree := by
  let s : Finset (Finset E) := Finset.univ.filter (fun F => ∀ x y : V, G.reaches F x y)
  have hs : s.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hconn
  obtain ⟨F, hF, hmin⟩ := s.exists_min_image Finset.card hs
  have hFc : ∀ x y : V, G.reaches F x y := (Finset.mem_filter.mp hF).2
  have hforest : G.is_forest F := by
    intro e he hcycle
    have hadj : ∀ x y, G.adjacent F x y → G.reaches (F.erase e) x y := by
      intro x y h
      obtain ⟨f, hf, hxy⟩ := h
      by_cases hfe : f = e
      · subst f
        rcases hxy with ⟨hl, hr⟩ | ⟨hr, hl⟩
        · simpa only [hl, hr] using hcycle
        · simpa only [hl, hr] using G.reaches_symm hcycle
      · exact .single ⟨f, Finset.mem_erase.mpr ⟨hfe,hf⟩, hxy⟩
    have herase : ∀ x y : V, G.reaches (F.erase e) x y := by
      intro x y
      induction hFc x y with
      | refl => exact .refl
      | tail h hxy ih => exact ih.trans (hadj _ _ hxy)
    have hemem : F.erase e ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact herase
    have hm := hmin (F.erase e) hemem
    exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem he)) hm
  refine ⟨⟨F, Set.univ_nonempty, ?_, ?_, hforest⟩⟩
  · intro e he
    exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  · intro x hx y hy
    exact hFc x y

end FiniteAvalanches.Trees.Multigraph
