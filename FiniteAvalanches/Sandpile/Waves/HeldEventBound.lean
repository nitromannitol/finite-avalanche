import FiniteAvalanches.Sandpile.Waves.AvalancheEvents
import FiniteAvalanches.Sandpile.Waves.BurnedSet

/-! The complete finite-avalanche bound after deterministic held burning. -/
namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Components
open scoped Classical
noncomputable section

/-- Held burning bounds the transition count before conditioning on a core shape. -/
theorem finite_avalanche_leaves_probability_le_held {N : ℕ} (o : FiniteWired.Active N)
    (S B : Finset Site2) (hS : nbrFinset (FiniteWired.site o) ⊆ S) :
    (FiniteWired.law N).real {η | finiteAvalancheLeaves o B η} ≤
      ((∑ g : Punctured N o,
        (if S ⊆ core g.val ∧ ¬S ⊆ heldInterior g.val (coreShape g.val)
          then 1 else 0 : ℝ)) +
      ∑ g : Punctured N o,
        (if ¬S ⊆ core g.val ∧ ¬core g.val ⊆ B then 1 else 0 : ℝ)) /
          Fintype.card (FiniteWired.Recurrent N) := by
  classical
  apply (finite_avalanche_leaves_probability_le o S B hS).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have ht := sum_inverse_transitions_le_held_interior o S
  apply add_le_add
  · with_reducible convert ht using 1
    all_goals first
      | (refine Finset.sum_congr ?_ ?_
         · ext g
           simp only [Finset.mem_univ]
         · intro g _
           split_ifs <;> rfl)
      | rfl
  · exact le_refl _

end
end FiniteAvalanches.Sandpile.Waves
