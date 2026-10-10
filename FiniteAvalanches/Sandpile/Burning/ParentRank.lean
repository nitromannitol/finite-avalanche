module

public import FiniteAvalanches.Sandpile.Burning.Layers
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! An actual burned vertex chooses a parent among the original copies entering
the immediately previous burning layer, by a fixed linear order on E. The height
interval and local reconstruction are derived from the actual layers. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

def parentCopies (h : SourceHeights G s) (n : ℕ) (v : SourceVertex s) : Finset E :=
  incidentInto G (previousBurnt G s h n) v.val

theorem burn_offset_lt (h : SourceHeights G s) (n : ℕ) (v : SourceVertex s)
    (hv : v ∈ burnLayer G s h n) :
    (h v).val - activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v <
      (parentCopies G s h n v).card := by
  have hlo := (mem_burn_layer G s h n v).mp hv
  change _ < degreeInto G (previousBurnt G s h n) v.val
  cases n with
  | zero =>
    simp only [burnRemainder] at hlo
    have hd := first_layer_degree G s v
    have hh := (h v).isLt
    change (h v).val - activeDegree G (Finset.univ.erase s) Finset.univ v < degreeInto G {s} v.val
    omega
  | succ n =>
    have hhi := (Finset.mem_filter.mp hlo.1).2
    have hd := later_layer_degree G s h n v
    omega

def burnOffset (h : SourceHeights G s) (n : ℕ)
    (v : {v : SourceVertex s // v ∈ burnLayer G s h n}) : Fin (parentCopies G s h n v.val).card :=
  ⟨(h v.val).val - activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v.val,
    burn_offset_lt G s h n v.val v.property⟩

variable [LinearOrder E]

/-- The increasing enumeration of every original parent-edge copy. -/
def parentCopyOrder (h : SourceHeights G s) (n : ℕ) (v : SourceVertex s) :
    Fin (parentCopies G s h n v).card ≃o {e : E // e ∈ parentCopies G s h n v} :=
  (parentCopies G s h n v).orderIsoOfFin rfl

/-- The actual copy chosen by the height offset; existence of its rank is already proved. -/
def burningParent (h : SourceHeights G s) (n : ℕ)
    (v : {v : SourceVertex s // v ∈ burnLayer G s h n}) :
    {e : E // e ∈ parentCopies G s h n v.val} :=
  parentCopyOrder G s h n v.val (burnOffset G s h n v)

theorem burning_parent_incident (h : SourceHeights G s) (n : ℕ)
    (v : {v : SourceVertex s // v ∈ burnLayer G s h n}) :
    (G.left (burningParent G s h n v).val = v.val.val ∧
      G.right (burningParent G s h n v).val ∈ previousBurnt G s h n) ∨
    (G.right (burningParent G s h n v).val = v.val.val ∧
      G.left (burningParent G s h n v).val ∈ previousBurnt G s h n) := by
  exact (Finset.mem_filter.mp (burningParent G s h n v).property).2

theorem burning_parent_rank (h : SourceHeights G s) (n : ℕ)
    (v : {v : SourceVertex s // v ∈ burnLayer G s h n}) :
    (parentCopyOrder G s h n v.val).symm (burningParent G s h n v) = burnOffset G s h n v :=
  (parentCopyOrder G s h n v.val).symm_apply_apply _

theorem burning_parent_reconstruct_height (h : SourceHeights G s) (n : ℕ)
    (v : {v : SourceVertex s // v ∈ burnLayer G s h n}) :
    ((parentCopyOrder G s h n v.val).symm (burningParent G s h n v)).val +
      activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v.val = (h v.val).val := by
  rw [burning_parent_rank]
  exact Nat.sub_add_cancel ((mem_burn_layer G s h n v.val).mp v.property).2

end
end FiniteAvalanches.Sandpile.Burning
