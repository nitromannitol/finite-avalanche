module

public import FiniteAvalanches.Trees.Measure

@[expose] public section

/-! Positive-support indexing is exactly positivity of the normalized tree product count. -/
open scoped Classical
namespace FiniteAvalanches.Trees.Multigraph
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Multigraph V E)

theorem tree_product_mass_pos_iff [Nonempty G.SpanningTree] (C : Set V) :
    0 < (Fintype.card (G.ComponentTree C) : ℝ) * Fintype.card (G.ComponentTree Cᶜ) /
      Fintype.card G.SpanningTree ↔
      0 < Fintype.card (G.ComponentTree C) ∧ 0 < Fintype.card (G.ComponentTree Cᶜ) := by
  have ht : (0 : ℝ) < Fintype.card G.SpanningTree := by exact_mod_cast Fintype.card_pos
  rw [div_pos_iff_of_pos_right ht, ← Nat.cast_mul, Nat.cast_pos]
  constructor
  · intro h
    constructor
    · by_contra hn
      have hz : Fintype.card (G.ComponentTree C) = 0 := by omega
      simp [hz] at h
    · by_contra hn
      have hz : Fintype.card (G.ComponentTree Cᶜ) = 0 := by omega
      simp [hz] at h
  · rintro ⟨hC, hD⟩
    exact Nat.mul_pos hC hD

end FiniteAvalanches.Trees.Multigraph
