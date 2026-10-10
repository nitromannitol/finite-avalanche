module

public import FiniteAvalanches.Sandpile.Burning.Trace
public import FiniteAvalanches.Sandpile.Burning.DegreeTransport

@[expose] public section

/-! Restrict an actual held burn to its actual stopping set. All height bounds
and no-forbidden tests are proved from that operational stopping set; no proposed
shape, product conclusion, recurrence bridge, or uniform law is supplied. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (U : Finset V)

theorem active_degree_union {A C : Finset (InducedVertex U)} (hd : Disjoint A C)
    (x : InducedVertex U) :
    activeDegree G U (A ∪ C) x = activeDegree G U A x + activeDegree G U C x := by
  unfold activeDegree
  rw [Finset.image_union]
  apply degree_into_union G
  apply Finset.disjoint_left.mpr
  intro v hvA hvC
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hvA
  obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hvC
  have he' : c = a := Subtype.ext he
  subst c
  exact Finset.disjoint_left.mp hd ha hc

theorem height_ge_active_degree_outside (h : Heights G U) (B : Finset (InducedVertex U))
    (x : InducedVertex U) (hx : x ∉ heldBurning G U h B) :
    activeDegree G U (heldBurning G U h B) x ≤ (h x).val := by
  let A := heldBurning G U h B
  obtain ⟨hc, hm⟩ := held_burning_largest G U h B
  by_contra hn
  have hclosed : heldClosed G U h B (insert x A) := by
    refine ⟨hc.1.trans (Finset.subset_insert _ _), ?_⟩
    intro y hy hyB
    rcases Finset.mem_insert.mp hy with he | hy
    · subst y
      have hd := active_degree_mono G U (Finset.subset_insert x A) x
      dsimp only [A] at hd ⊢
      omega
    · exact lt_of_lt_of_le (hc.2 y hy hyB)
        (active_degree_mono G U (Finset.subset_insert x A) y)
  exact hx (hm _ hclosed (Finset.mem_insert_self ..))

theorem inner_height_stable (h : Heights G U) (B : Finset (InducedVertex U))
    (x : InducedVertex U) (hx : x ∈ heldBurning G U h B) :
    (h x).val < if x ∈ B then degree G x.val else activeDegree G U (heldBurning G U h B) x := by
  by_cases hb : x ∈ B
  · simpa only [if_pos hb] using (h x).isLt
  · simpa only [if_neg hb] using (held_burning_largest G U h B).1.2 x hx hb

theorem outer_shift_stable (h : Heights G U) (B : Finset (InducedVertex U))
    (x : InducedVertex U) (hx : x ∉ heldBurning G U h B) :
    (h x).val - activeDegree G U (heldBurning G U h B) x <
      degree G x.val - activeDegree G U (heldBurning G U h B) x := by
  have hlo := height_ge_active_degree_outside G U h B x hx
  have hhi := (h x).isLt
  have hd := degree_into_le_degree G ((heldBurning G U h B).image Subtype.val) x.val
  change activeDegree G U (heldBurning G U h B) x ≤ degree G x.val at hd
  omega

theorem outer_shift_no_forbidden (h : Heights G U) (B : Finset (InducedVertex U))
    (H : Finset (InducedVertex U)) (hH : H ⊆ Finset.univ \ heldBurning G U h B) :
    ¬(H.Nonempty ∧ ∀ x ∈ H,
      (h x).val - activeDegree G U (heldBurning G U h B) x < activeDegree G U H x) := by
  intro hf
  let A := heldBurning G U h B
  obtain ⟨hc, hm⟩ := held_burning_largest G U h B
  have hd : Disjoint A H := Finset.disjoint_left.mpr (fun x hx hxH =>
    (Finset.mem_sdiff.mp (hH hxH)).2 hx)
  have hclosed : heldClosed G U h B (A ∪ H) := by
    refine ⟨hc.1.trans Finset.subset_union_left, ?_⟩
    intro x hx hxB
    rcases Finset.mem_union.mp hx with hx | hx
    · exact lt_of_lt_of_le (hc.2 x hx hxB)
        (active_degree_mono G U Finset.subset_union_left x)
    · have hh := hf.2 x hx
      have hlo := height_ge_active_degree_outside G U h B x
        (Finset.mem_sdiff.mp (hH hx)).2
      rw [active_degree_union G U hd]
      dsimp only [A]
      omega
  obtain ⟨x, hx⟩ := hf.1
  exact (Finset.mem_sdiff.mp (hH hx)).2 (hm _ hclosed (Finset.mem_union_right _ hx))

/-- Unchanged inner heights on every unburnt vertex, using exactly the held-graph degree. -/
def innerRestriction (h : Heights G U) (B : Finset (InducedVertex U)) :
    (x : {x : InducedVertex U // x ∈ heldBurning G U h B}) →
      Fin (if x.val ∈ B then degree G x.val.val
        else activeDegree G U (heldBurning G U h B) x.val) :=
  fun x => ⟨(h x.val).val, inner_height_stable G U h B x.val x.property⟩

/-- Outer heights subtract exactly the original copies entering the final unburnt set. -/
def outerRestriction (h : Heights G U) (B : Finset (InducedVertex U)) :
    (x : {x : InducedVertex U // x ∉ heldBurning G U h B}) →
      Fin (degree G x.val.val - activeDegree G U (heldBurning G U h B) x.val) :=
  fun x => ⟨(h x.val).val - activeDegree G U (heldBurning G U h B) x.val,
    outer_shift_stable G U h B x.val x.property⟩

theorem outer_restriction_add (h : Heights G U) (B : Finset (InducedVertex U))
    (x : {x : InducedVertex U // x ∉ heldBurning G U h B}) :
    (outerRestriction G U h B x).val + activeDegree G U (heldBurning G U h B) x.val =
      (h x.val).val :=
  Nat.sub_add_cancel (height_ge_active_degree_outside G U h B x.val x.property)

end
end FiniteAvalanches.Sandpile.Burning
