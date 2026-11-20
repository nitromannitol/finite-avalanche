import FiniteAvalanches.Wilson.Lattice.WiredDualCopies

/-! The shifted square of dual faces adjacent to wired-box edge copies. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Face labels adjacent to the wired square box form an even-sided square. -/
def inDualFaceBox (B : ℕ) (z : Site 2) : Prop :=
  ∀ i, -(B : ℤ) - 1 ≤ z i ∧ z i ≤ B

/-- The lower-left base of the primal edge traversed in a signed direction. -/
def signedStepBase (z : Site 2) (d : FiniteWired.Direction) : Site 2 :=
  if d.2 then z else z - unit d.1

/-- The positive-coordinate base and direction of its crossing dual edge. -/
def crossingStepBase (z : Site 2) (d : FiniteWired.Direction) : Site 2 × Fin 2 :=
  (signedStepBase z d - unit (1 - d.1), 1 - d.1)

/-- The two faces beside any edge incident to a box vertex lie in the dual face box. -/
theorem crossingStepBase_faces_inDualFaceBox (B : ℕ) (z : Site 2)
    (hz : FiniteWired.inBox B z) (d : FiniteWired.Direction) :
    inDualFaceBox B (crossingStepBase z d).1 ∧
      inDualFaceBox B ((crossingStepBase z d).1 + unit (crossingStepBase z d).2) := by
  have h0 := hz 0
  have h1 := hz 1
  rcases d with ⟨i, b⟩
  fin_cases i <;> cases b <;>
    simp only [inDualFaceBox, crossingStepBase, signedStepBase, Bool.false_eq_true,
      if_false, if_true, Fin.forall_fin_two, Pi.add_apply, Pi.sub_apply, unit, Pi.single_apply] <;>
    norm_num <;> omega

/-- The dual of a signed lattice step is the edge between its two adjacent face labels. -/
theorem crossingEdgeEquiv_symm_direction_step (z : Site 2) (d : FiniteWired.Direction) :
    crossingEdgeEquiv.symm ⟨s(z, z + FiniteWired.step d), lattice_adj_direction_step z d⟩ =
      baseEdge (crossingStepBase z d) := by
  rcases d with ⟨i, b⟩
  cases b
  · have he : (⟨s(z, z + FiniteWired.step (i, false)),
          lattice_adj_direction_step z (i, false)⟩ : LatticeEdge) = baseEdge (z - unit i, i) := by
      apply Subtype.ext
      simp only [FiniteWired.step, Bool.false_eq_true, if_false, ← sub_eq_add_neg, baseEdge]
      rw [sub_add_cancel]
      exact Sym2.eq_swap
    rw [he, crossingEdgeEquiv_symm_baseEdge]
    rfl
  · have he : (⟨s(z, z + FiniteWired.step (i, true)),
          lattice_adj_direction_step z (i, true)⟩ : LatticeEdge) = baseEdge (z, i) := by
      apply Subtype.ext
      simp [FiniteWired.step, baseEdge]
    rw [he, crossingEdgeEquiv_symm_baseEdge]
    rfl

/-- Every dual edge crossing a wired copy has both endpoints in the dual face box. -/
theorem wiredCopyDualEdge_endpoints_inDualFaceBox (B : ℕ) (e : FiniteWired.Edge B) :
    ∀ z ∈ (wiredCopyDualEdge e).val, inDualFaceBox B z := by
  have hstep (z : Site 2) (hz : FiniteWired.inBox B z) (d : FiniteWired.Direction) :
      ∀ w ∈ (crossingEdgeEquiv.symm
          ⟨s(z, z + FiniteWired.step d), lattice_adj_direction_step z d⟩).val,
        inDualFaceBox B w := by
    rw [crossingEdgeEquiv_symm_direction_step]
    intro w hw
    have hm : w = (crossingStepBase z d).1 ∨
        w = (crossingStepBase z d).1 + unit (crossingStepBase z d).2 := by
      simpa only [baseEdge, Sym2.mem_iff] using hw
    rcases hm with rfl | rfl
    · exact (crossingStepBase_faces_inDualFaceBox B z hz d).1
    · exact (crossingStepBase_faces_inDualFaceBox B z hz d).2
  cases e with
  | inr e =>
    exact hstep (FiniteWired.site e.val.1) (fun j => (e.val.1 j).property) e.val.2
  | inl e =>
    obtain ⟨i, hi⟩ := e.property
    have he : wiredCopyLatticeEdge (.inl e) =
        ⟨s(FiniteWired.site e.val.1, FiniteWired.site e.val.1 + FiniteWired.step (i, true)),
          lattice_adj_direction_step (FiniteWired.site e.val.1) (i, true)⟩ := by
      apply Subtype.ext
      change s(FiniteWired.site e.val.1, FiniteWired.site e.val.2) =
        s(FiniteWired.site e.val.1, FiniteWired.site e.val.1 + FiniteWired.step (i, true))
      simp only [FiniteWired.step, if_true]
      rw [hi]
    change ∀ z ∈ (crossingEdgeEquiv.symm (wiredCopyLatticeEdge (.inl e))).val, inDualFaceBox B z
    rw [he]
    exact hstep (FiniteWired.site e.val.1) (fun j => (e.val.1 j).property) (i, true)

end
end FiniteAvalanches.Wilson.Lattice
