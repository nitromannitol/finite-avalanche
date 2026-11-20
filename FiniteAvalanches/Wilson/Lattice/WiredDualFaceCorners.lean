import FiniteAvalanches.Wilson.Lattice.WiredDualFaceGraph
import FiniteAvalanches.Wilson.Lattice.WiredActiveStackLaw

/-! The four dual faces around each active wired vertex. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- A face adjacent to a lattice site, indexed by its two coordinate offsets. -/
def dualFaceCornerSite (z : Site 2) (a b : Bool) : Site 2 :=
  z - (if a then unit 0 else 0) - (if b then unit 1 else 0)

/-- All four face corners of an active vertex belong to the dual face square. -/
theorem dualFaceCornerSite_in_box (B : ℕ) (x : FiniteWired.Active B) (a b : Bool) :
    inDualFaceBox B (dualFaceCornerSite (FiniteWired.site x) a b) := by
  have h0 := (x 0).property
  have h1 := (x 1).property
  change -(B : ℤ) ≤ FiniteWired.site x 0 ∧ FiniteWired.site x 0 ≤ B at h0
  change -(B : ℤ) ≤ FiniteWired.site x 1 ∧ FiniteWired.site x 1 ≤ B at h1
  cases a <;> cases b <;>
    simp only [inDualFaceBox, Fin.forall_fin_two, dualFaceCornerSite, Pi.sub_apply,
      Pi.zero_apply, Bool.false_eq_true, if_false, if_true, unit, Pi.single_apply] <;>
    norm_num at * <;> omega

/-- The actual face-square vertex at a specified corner of an active vertex. -/
def wiredDualFaceCorner (B : ℕ) (x : FiniteWired.Active B) (a b : Bool) : WiredDualFace B :=
  wiredDualFaceOfSite B (dualFaceCornerSite (FiniteWired.site x) a b)
    (dualFaceCornerSite_in_box B x a b)

/-- The crossing face edge of a direction copy joins the two faces beside that step. -/
theorem wiredDualFaceGraph_directionEdge (B : ℕ) (x : FiniteWired.Active B)
    (d : FiniteWired.Direction) :
    s(wiredDualFaceSite ((wiredDualFaceGraph B).left (FiniteWired.directionEdge x d)),
      wiredDualFaceSite ((wiredDualFaceGraph B).right (FiniteWired.directionEdge x d))) =
      s((crossingStepBase (FiniteWired.site x) d).1,
        (crossingStepBase (FiniteWired.site x) d).1 + unit (crossingStepBase (FiniteWired.site x) d).2) := by
  rw [wiredDualFaceGraph_edge]
  change (crossingEdgeEquiv.symm (wiredCopyLatticeEdge (FiniteWired.directionEdge x d))).val = _
  rw [wiredCopyLatticeEdge_directionEdge, crossingEdgeEquiv_symm_direction_step]
  rfl

/-- The two dual faces crossing a positive horizontal step. -/
theorem wiredDualFaceGraph_direction_zero_true (B : ℕ) (x : FiniteWired.Active B) :
    s((wiredDualFaceGraph B).left (FiniteWired.directionEdge x (0, true)),
      (wiredDualFaceGraph B).right (FiniteWired.directionEdge x (0, true))) =
      s(wiredDualFaceCorner B x false true, wiredDualFaceCorner B x false false) := by
  apply Sym2.map.injective (wiredDualFaceSite_injective B)
  rw [Sym2.map_mk, wiredDualFaceGraph_directionEdge, Sym2.map_mk]
  apply congrArg₂ (fun (a b : Site 2) => s(a, b)) <;> simp [wiredDualFaceCorner, wiredDualFaceSite_ofSite, dualFaceCornerSite, crossingStepBase, signedStepBase] <;> abel

/-- The two dual faces crossing a negative horizontal step. -/
theorem wiredDualFaceGraph_direction_zero_false (B : ℕ) (x : FiniteWired.Active B) :
    s((wiredDualFaceGraph B).left (FiniteWired.directionEdge x (0, false)),
      (wiredDualFaceGraph B).right (FiniteWired.directionEdge x (0, false))) =
      s(wiredDualFaceCorner B x true true, wiredDualFaceCorner B x true false) := by
  apply Sym2.map.injective (wiredDualFaceSite_injective B)
  rw [Sym2.map_mk, wiredDualFaceGraph_directionEdge, Sym2.map_mk]
  apply congrArg₂ (fun (a b : Site 2) => s(a, b)) <;> simp [wiredDualFaceCorner, wiredDualFaceSite_ofSite, dualFaceCornerSite, crossingStepBase, signedStepBase] <;> abel

/-- The two dual faces crossing a positive vertical step. -/
theorem wiredDualFaceGraph_direction_one_true (B : ℕ) (x : FiniteWired.Active B) :
    s((wiredDualFaceGraph B).left (FiniteWired.directionEdge x (1, true)),
      (wiredDualFaceGraph B).right (FiniteWired.directionEdge x (1, true))) =
      s(wiredDualFaceCorner B x true false, wiredDualFaceCorner B x false false) := by
  apply Sym2.map.injective (wiredDualFaceSite_injective B)
  rw [Sym2.map_mk, wiredDualFaceGraph_directionEdge, Sym2.map_mk]
  apply congrArg₂ (fun (a b : Site 2) => s(a, b)) <;> simp [wiredDualFaceCorner, wiredDualFaceSite_ofSite, dualFaceCornerSite, crossingStepBase, signedStepBase] <;> abel

/-- The two dual faces crossing a negative vertical step. -/
theorem wiredDualFaceGraph_direction_one_false (B : ℕ) (x : FiniteWired.Active B) :
    s((wiredDualFaceGraph B).left (FiniteWired.directionEdge x (1, false)),
      (wiredDualFaceGraph B).right (FiniteWired.directionEdge x (1, false))) =
      s(wiredDualFaceCorner B x true true, wiredDualFaceCorner B x false true) := by
  apply Sym2.map.injective (wiredDualFaceSite_injective B)
  rw [Sym2.map_mk, wiredDualFaceGraph_directionEdge, Sym2.map_mk]
  apply congrArg₂ (fun (a b : Site 2) => s(a, b)) <;> simp [wiredDualFaceCorner, wiredDualFaceSite_ofSite, dualFaceCornerSite, crossingStepBase, signedStepBase] <;> abel

end
end FiniteAvalanches.Wilson.Lattice
