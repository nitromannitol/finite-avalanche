import FiniteAvalanches.Wilson.Lattice.WiredDualFaceStacks
import FiniteAvalanches.Wilson.Lattice.FreeWordCoupling

/-! Confined direction words agree in the centered box and dual face square. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Follow a lattice direction inside the dual face square, staying put if it exits. -/
def wiredDualFaceDirectionHead (B : ℕ) (v : WiredDualFace B) (d : FiniteWired.Direction) :
    WiredDualFace B :=
  if h : inDualFaceBox B (wiredDualFaceSite v + FiniteWired.step d) then
    wiredDualFaceOfSite B (wiredDualFaceSite v + FiniteWired.step d) h else v

/-- Inside the centered interior, the direction successor commutes with inclusion. -/
theorem wiredDualFaceDirectionHead_inner (B : ℕ) (x : FiniteWired.Active (B + 1))
    (hx : FiniteWired.inBox B (FiniteWired.site x)) (d : FiniteWired.Direction) :
    wiredDualFaceDirectionHead (B + 1) (wiredDualFaceInnerVertex (B + 1) x) d =
      wiredDualFaceInnerVertex (B + 1) (freeDirectionHead (B + 1) x d) := by
  have hn := inBox_succ_of_step B (FiniteWired.site x) hx d
  have hd := inDualFaceBox_of_inBox (B + 1) _ hn
  apply wiredDualFaceSite_injective (B + 1)
  simp only [wiredDualFaceDirectionHead, wiredDualFaceSite_innerVertex, dif_pos hd,
    wiredDualFaceSite_ofSite, freeDirectionHead, dif_pos hn, FiniteWired.site_activeOfSite]

/-- In the centered interior the direction step is the actual face incident-copy step. -/
theorem wiredDualFaceDirectionHead_eq_incident (B : ℕ) (x : FiniteWired.Active (B + 1))
    (hx : FiniteWired.inBox B (FiniteWired.site x)) (d : FiniteWired.Direction) :
    incidentCopyHead (wiredDualFaceGraph (B + 1)) (wiredDualFaceInnerVertex (B + 1) x)
        (wiredDualFaceInteriorDirectionEquiv B x hx d) =
      wiredDualFaceDirectionHead (B + 1) (wiredDualFaceInnerVertex (B + 1) x) d := by
  rw [wiredDualFaceInteriorDirection_head B x hx d, freeInteriorDirection_head_eq B x hx d,
    wiredDualFaceDirectionHead_inner B x hx d]

/-- A direction word confined to the inner box visits corresponding vertices. -/
theorem wiredDualFace_wordState_of_confined (B : ℕ) (x : FiniteWired.Active (B + 1))
    (k : Cursor (FiniteWired.Active (B + 1))) (l : Cursor (WiredDualFace (B + 1)))
    (w : ℕ → FiniteWired.Direction) (n : ℕ)
    (hconf : ∀ i < n, FiniteWired.inBox B
      (FiniteWired.site (wordState (freeDirectionHead (B + 1)) x k w i).1)) :
    ∀ i ≤ n, wiredDualFaceInnerVertex (B + 1)
        (wordState (freeDirectionHead (B + 1)) x k w i).1 =
      (wordState (wiredDualFaceDirectionHead (B + 1))
        (wiredDualFaceInnerVertex (B + 1) x) l w i).1 := by
  apply wordState_map_fst_of_steps (freeDirectionHead (B + 1))
    (wiredDualFaceDirectionHead (B + 1)) (wiredDualFaceInnerVertex (B + 1)) x _ k l w n rfl
  intro i hi
  exact (wiredDualFaceDirectionHead_inner B _ (hconf i hi) (w i)).symm

/-- Loop erasure of a confined word is preserved by the centered-box inclusion. -/
theorem wiredDualFace_wordTrace_loopErase_of_confined (B : ℕ)
    (x : FiniteWired.Active (B + 1))
    (k : Cursor (FiniteWired.Active (B + 1))) (l : Cursor (WiredDualFace (B + 1)))
    (w : ℕ → FiniteWired.Direction) (n : ℕ)
    (hconf : ∀ i < n, FiniteWired.inBox B
      (FiniteWired.site (wordState (freeDirectionHead (B + 1)) x k w i).1)) :
    letI : Quiver (FiniteWired.Active (B + 1)) := instructionQuiver (freeDirectionHead (B + 1))
    letI : Quiver (WiredDualFace (B + 1)) := instructionQuiver (wiredDualFaceDirectionHead (B + 1))
    (loopErase (wordTrace (freeDirectionHead (B + 1)) x w n).2).vertices.map
        (wiredDualFaceInnerVertex (B + 1)) =
      (loopErase (wordTrace (wiredDualFaceDirectionHead (B + 1))
        (wiredDualFaceInnerVertex (B + 1) x) w n).2).vertices := by
  apply wordTrace_loopErase_map_of_steps (freeDirectionHead (B + 1))
    (wiredDualFaceDirectionHead (B + 1)) (wiredDualFaceInnerVertex (B + 1))
    (wiredDualFaceInnerVertex_injective (B + 1)) x _ k l w n rfl
  intro i hi
  exact (wiredDualFaceDirectionHead_inner B _ (hconf i hi) (w i)).symm

end
end FiniteAvalanches.Wilson.Lattice
