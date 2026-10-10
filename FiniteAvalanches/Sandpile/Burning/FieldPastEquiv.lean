module

public import FiniteAvalanches.Sandpile.Burning.PastTreeEquiv
public import FiniteAvalanches.Sandpile.Burning.TreeFields

@[expose] public section

/-! Compose the actual two-phase field bijection with the proved tree lift.
This matches held stopping fibers with literal rooted-past fibers. No probability
or Markov recurrence criterion is an input. Invalid shapes have empty fibers. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

abbrev AllowedField := {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h}

/-- The actual past union reindexed by the nonsink subtype, after sink exclusion. -/
def sourcePastUnion (t : (copiedTreeGraph G).SpanningTree) (B : Finset (SourceVertex s)) :
    Finset (SourceVertex s) := Finset.univ.filter fun x => x.val ∈ treePastUnion G s t B

theorem mem_source_past_union (t : (copiedTreeGraph G).SpanningTree)
    (B : Finset (SourceVertex s)) (x : SourceVertex s) :
    x ∈ sourcePastUnion G s t B ↔ x.val ∈ treePastUnion G s t B := by
  simp [sourcePastUnion]

theorem source_past_union_image (t : (copiedTreeGraph G).SpanningTree)
    (B : Finset (SourceVertex s)) :
    (sourcePastUnion G s t B).image Subtype.val = treePastUnion G s t B := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_source_past_union G s t B v).mp hv
  · intro hx
    have hxs : x ≠ s := by intro he; exact tree_past_union_avoids_sink G s t B (he ▸ hx)
    let v : SourceVertex s := ⟨x, Finset.mem_erase.mpr ⟨hxs, Finset.mem_univ _⟩⟩
    exact Finset.mem_image.mpr ⟨v, (mem_source_past_union G s t B v).mpr hx, rfl⟩

theorem source_past_union_contains_held (t : (copiedTreeGraph G).SpanningTree)
    (B : Finset (SourceVertex s)) : B ⊆ sourcePastUnion G s t B := by
  intro b hb
  exact (mem_source_past_union G s t B b).mpr
    (held_subset_tree_past_union G s t B (Finset.mem_image_of_mem Subtype.val hb))

theorem source_past_union_eq_iff (t : (copiedTreeGraph G).SpanningTree)
    (B A : Finset (SourceVertex s)) :
    sourcePastUnion G s t B = A ↔ treePastUnion G s t B = A.image Subtype.val := by
  constructor
  · intro h
    rw [← source_past_union_image G s t B, h]
  · intro h
    ext x
    rw [mem_source_past_union, h, subtype_mem_image_iff]

/-- Nesting the allowed-field subtype does not change any field coordinate. -/
def heldAllowedFiberEquiv (B A : Finset (SourceVertex s)) :
    {h : AllowedField G s // heldBurning G (Finset.univ.erase s) h.val B = A} ≃
      {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h ∧
        heldBurning G (Finset.univ.erase s) h B = A} where
  toFun h := ⟨h.val.val, h.val.property, h.property⟩
  invFun h := ⟨⟨h.val, h.property.1⟩, h.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sourcePastFiberEquiv (B A : Finset (SourceVertex s)) :
    {t : (copiedTreeGraph G).SpanningTree // sourcePastUnion G s t B = A} ≃
      HeldPastTreeFiber G s B (A.image Subtype.val) where
  toFun t := ⟨t.val, (source_past_union_eq_iff G s t.val B A).mp t.property⟩
  invFun t := ⟨t.val, (source_past_union_eq_iff G s t.val B A).mpr t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full field/past-fiber bijection, using complement-first literal tree restrictions. -/
def heldFieldPastEquiv (B A : Finset (SourceVertex s)) (hBA : B ⊆ A) :
    {h : AllowedField G s // heldBurning G (Finset.univ.erase s) h.val B = A} ≃
      {t : (copiedTreeGraph G).SpanningTree // sourcePastUnion G s t B = A} :=
  (heldAllowedFiberEquiv G s B A).trans
    ((heldGraphTreeEquiv G s B A hBA).trans
      ((heldPastTreeEquiv G s B (A.image Subtype.val) (source_shape_avoids_sink s A)
        (source_shape_subset s B A hBA)).symm.trans (sourcePastFiberEquiv G s B A).symm))

/-- Equality of counts for every shape, including shapes not containing B. -/
theorem card_held_stop_eq_past (B A : Finset (SourceVertex s)) :
    Nat.card {h : AllowedField G s // heldBurning G (Finset.univ.erase s) h.val B = A} =
      Nat.card {t : (copiedTreeGraph G).SpanningTree // sourcePastUnion G s t B = A} := by
  by_cases hBA : B ⊆ A
  · exact Nat.card_congr (heldFieldPastEquiv G s B A hBA)
  · letI : IsEmpty {h : AllowedField G s // heldBurning G (Finset.univ.erase s) h.val B = A} :=
      ⟨fun h => hBA (h.property ▸ (held_burning_largest G (Finset.univ.erase s) h.val.val B).1.1)⟩
    letI : IsEmpty {t : (copiedTreeGraph G).SpanningTree // sourcePastUnion G s t B = A} :=
      ⟨fun t => hBA (t.property ▸ source_past_union_contains_held G s t.val B)⟩
    simp [Nat.card_eq_fintype_card]

/-- The denominator counts the whole original allowed carrier. -/
theorem card_allowed_eq_trees : Nat.card (AllowedField G s) =
    Nat.card (copiedTreeGraph G).SpanningTree := Nat.card_congr (burningEquiv G s)

end
end FiniteAvalanches.Sandpile.Burning
