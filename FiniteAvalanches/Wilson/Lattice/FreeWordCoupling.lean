import FiniteAvalanches.Wilson.Lattice.FreeStoppedExploration
import FiniteAvalanches.Wilson.Lattice.WiredWordCoupling

/-! Common-increment coupling of lattice walks and free-box walks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Project a lattice site into a free box, using the origin outside the box. -/
def freeSite (B : ℕ) (z : Site 2) : FiniteWired.Active B :=
  if h : FiniteWired.inBox B z then FiniteWired.activeOfSite B z h else wiredOrigin B

/-- On sites inside the box, the projection followed by the site map is the identity. -/
theorem site_freeSite_of_inBox (B : ℕ) (z : Site 2) (hz : FiniteWired.inBox B z) :
    FiniteWired.site (freeSite B z) = z := by
  simp only [freeSite, dif_pos hz, FiniteWired.site_activeOfSite]

/-- Inside the box the free successor agrees with the original lattice step. -/
theorem freeDirectionHead_freeSite_of_inBox (B : ℕ) (z : Site 2)
    (d : FiniteWired.Direction) (hz : FiniteWired.inBox B z)
    (hnext : FiniteWired.inBox B (z + FiniteWired.step d)) :
    freeDirectionHead B (freeSite B z) d = freeSite B (z + FiniteWired.step d) := by
  apply FiniteWired.site_injective B
  simp [freeDirectionHead, site_freeSite_of_inBox B z hz, hnext,
    site_freeSite_of_inBox B _ hnext, FiniteWired.site_activeOfSite]

/-- A confined free-box walk is the projected lattice walk with the same directions. -/
theorem freeWordState_eq_of_confined (B : ℕ) (x : Site 2) (w : WalkDriver)
    (k : Cursor (FiniteWired.Active B)) (n : ℕ)
    (hbox : ∀ i ≤ n, FiniteWired.inBox B (position x w i)) :
    ∀ i ≤ n, (wordState (freeDirectionHead B) (freeSite B x) k w i).1 =
      freeSite B (position x w i) := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    have hp := ih (Nat.le_trans (Nat.le_succ i) hi)
    change freeDirectionHead B (wordState (freeDirectionHead B) (freeSite B x) k w i).1 (w i) =
      freeSite B (position x w (i + 1))
    rw [hp, position_succ]
    exact freeDirectionHead_freeSite_of_inBox B _ _ (hbox i (Nat.le_trans (Nat.le_succ i) hi))
      (by simpa only [← position_succ] using hbox (i + 1) hi)

/-- A confined free-box word has the same loop erasure as the lattice word. -/
theorem freeWordTrace_loopErase_of_confined (B : ℕ) (x : Site 2) (w : WalkDriver)
    (k : Cursor (FiniteWired.Active B)) (n : ℕ)
    (hbox : ∀ i ≤ n, FiniteWired.inBox B (position x w i)) :
    letI : Quiver (FiniteWired.Active B) := instructionQuiver (freeDirectionHead B)
    ((loopErase (wordTrace (freeDirectionHead B) (freeSite B x) w n).2).vertices.map
      (FiniteWired.site : FiniteWired.Active B → Site 2)) = walkErase x w n := by
  letI : Quiver (FiniteWired.Active B) := instructionQuiver (freeDirectionHead B)
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  have h := wordTrace_loopErase_map_eq (freeDirectionHead B) latticeDirectionHead
    FiniteWired.site (FiniteWired.site_injective B) (freeSite B x) x w n ?_
  · rw [wordTrace_lattice_loopErase_vertices x w n] at h
    exact h
  · intro i hi
    rw [wordTrace_fst_eq_wordState (freeDirectionHead B) (freeSite B x) k w,
      freeWordState_eq_of_confined B x w k n hbox i hi,
      site_freeSite_of_inBox B _ (hbox i hi), wordTrace_lattice_position]

end
end FiniteAvalanches.Wilson.Lattice
