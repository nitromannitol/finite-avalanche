module

public import FiniteAvalanches.Sandpile.Burning.ParentRank

@[expose] public section

/-! Ordered original parent copies are in bijection with the actual one-vertex
burning height interval. Both inverses are explicit. This local bijection does
not assert that independent height changes preserve global burning layers. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

theorem parent_height_degree_le (h : SourceHeights G s) (n : ℕ) (v : SourceVertex s) :
    activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v +
      (parentCopies G s h n v).card ≤ degree G v.val := by
  change _ + degreeInto G (previousBurnt G s h n) v.val ≤ _
  cases n with
  | zero => exact le_of_eq (first_layer_degree G s v)
  | succ n =>
    rw [later_layer_degree]
    exact degree_into_le_degree G ((burnRemainder G s h n).image Subtype.val) v.val

/-- Stable heights in precisely the local interval encoded by previous-layer parent copies. -/
abbrev BurnHeight (h : SourceHeights G s) (n : ℕ) (v : SourceVertex s) :=
  {k : Fin (degree G v.val) //
    activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v ≤ k.val ∧
    k.val < activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v +
      (parentCopies G s h n v).card}

variable [LinearOrder E]

def burnHeightEquiv (h : SourceHeights G s) (n : ℕ) (v : SourceVertex s) :
    {e : E // e ∈ parentCopies G s h n v} ≃ BurnHeight G s h n v where
  toFun e :=
    let i := (parentCopyOrder G s h n v).symm e
    ⟨⟨i.val + activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v, by
      have hi := i.isLt
      have hd := parent_height_degree_le G s h n v
      omega⟩, by dsimp only; have hi := i.isLt; constructor <;> omega⟩
  invFun k := parentCopyOrder G s h n v
    ⟨k.val.val - activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v,
      by have hp := k.property; omega⟩
  left_inv e := by
    change parentCopyOrder G s h n v _ = e
    rw [← (parentCopyOrder G s h n v).apply_symm_apply e]
    congr 1
    apply Fin.ext
    simp
  right_inv k := by
    apply Subtype.ext
    apply Fin.ext
    simp only [OrderIso.symm_apply_apply]
    exact Nat.sub_add_cancel k.property.1

theorem burn_height_equiv_actual (h : SourceHeights G s) (n : ℕ)
    (v : {v : SourceVertex s // v ∈ burnLayer G s h n}) :
    (burnHeightEquiv G s h n v.val (burningParent G s h n v)).val = h v.val := by
  apply Fin.ext
  exact burning_parent_reconstruct_height G s h n v

end
end FiniteAvalanches.Sandpile.Burning
