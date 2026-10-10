module

public import FiniteAvalanches.Sandpile.Burning.ParentRank
public import FiniteAvalanches.Sandpile.Burning.Times

@[expose] public section

/-! Every active vertex of an allowed field has one actual original parent copy.
Its other endpoint is the sink or is in the immediately preceding burning layer.
This defines the selected copy set; a spanning-tree claim is not assumed. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

def globalParentCopy (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v : SourceVertex s) : {e : E // e ∈ parentCopies G s h (burnTime G s h hn v) v} :=
  burningParent G s h (burnTime G s h hn v) ⟨v, burn_time_spec G s h hn v⟩

theorem global_parent_incident (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v : SourceVertex s) :
    (G.left (globalParentCopy G s h hn v).val = v.val ∧
      G.right (globalParentCopy G s h hn v).val ∈ previousBurnt G s h (burnTime G s h hn v)) ∨
    (G.right (globalParentCopy G s h hn v).val = v.val ∧
      G.left (globalParentCopy G s h hn v).val ∈ previousBurnt G s h (burnTime G s h hn v)) :=
  burning_parent_incident G s h (burnTime G s h hn v) ⟨v, burn_time_spec G s h hn v⟩

theorem global_parent_previous (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v : SourceVertex s) (w : V)
    (hw : (G.left (globalParentCopy G s h hn v).val = v.val ∧
        G.right (globalParentCopy G s h hn v).val = w) ∨
      (G.right (globalParentCopy G s h hn v).val = v.val ∧
        G.left (globalParentCopy G s h hn v).val = w)) :
    w = s ∨ ∃ x : SourceVertex s, x.val = w ∧ burnTime G s h hn x + 1 = burnTime G s h hn v := by
  have hi := global_parent_incident G s h hn v
  have hl := G.loopless (globalParentCopy G s h hn v).val
  have hm : w ∈ previousBurnt G s h (burnTime G s h hn v) := by
    rcases hi with hi | hi <;> rcases hw with hw | hw <;> aesop
  cases ht : burnTime G s h hn v with
  | zero => exact Or.inl (by simpa only [ht, previousBurnt, Finset.mem_singleton] using hm)
  | succ n =>
    rw [ht] at hm
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hm
    refine Or.inr ⟨x, he, ?_⟩
    rw [(burn_time_eq_iff G s h hn x n).mpr hx]

theorem global_parent_other_time (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v w : SourceVertex s)
    (hw : (G.left (globalParentCopy G s h hn v).val = v.val ∧
        G.right (globalParentCopy G s h hn v).val = w.val) ∨
      (G.right (globalParentCopy G s h hn v).val = v.val ∧
        G.left (globalParentCopy G s h hn v).val = w.val)) :
    burnTime G s h hn w + 1 = burnTime G s h hn v := by
  rcases global_parent_previous G s h hn v w.val hw with hs | ⟨x, he, ht⟩
  · exact False.elim (source_vertex_ne_sink s w hs)
  · have hx : x = w := Subtype.ext he
    exact hx ▸ ht

theorem global_parent_injective (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h) :
    Function.Injective (fun v : SourceVertex s => (globalParentCopy G s h hn v).val) := by
  intro v w he
  change (globalParentCopy G s h hn v).val = (globalParentCopy G s h hn w).val at he
  have hv := global_parent_incident G s h hn v
  have hw := global_parent_incident G s h hn w
  rw [← he] at hw
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · exact Subtype.ext (hv.1.symm.trans hw.1)
  · have ht1 := global_parent_other_time G s h hn v w (Or.inl ⟨hv.1, hw.1⟩)
    have ht2 := global_parent_other_time G s h hn w v (Or.inr ⟨by rw [← he]; exact hw.1,
      by rw [← he]; exact hv.1⟩)
    omega
  · have ht1 := global_parent_other_time G s h hn v w (Or.inr ⟨hv.1, hw.1⟩)
    have ht2 := global_parent_other_time G s h hn w v (Or.inl ⟨by rw [← he]; exact hw.1,
      by rw [← he]; exact hv.1⟩)
    omega
  · exact Subtype.ext (hv.1.symm.trans hw.1)

def parentEdgeSet (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h) : Finset E :=
  Finset.univ.image fun v : SourceVertex s => (globalParentCopy G s h hn v).val

theorem parent_edge_set_card (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h) :
    (parentEdgeSet G s h hn).card = Fintype.card (SourceVertex s) := by
  unfold parentEdgeSet
  rw [Finset.card_image_of_injective _ (global_parent_injective G s h hn), Finset.card_univ]

end
end FiniteAvalanches.Sandpile.Burning
