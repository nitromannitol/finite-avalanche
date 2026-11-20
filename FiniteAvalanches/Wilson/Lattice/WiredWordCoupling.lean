import FiniteAvalanches.Wilson.CyclePopping.WordErasureNaturality
import FiniteAvalanches.Wilson.Lattice.RowSamplerBridge
import FiniteAvalanches.Wilson.Lattice.WiredStack

/-! Common-increment coupling of lattice walks and walks on a wired box. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Represent the wired vertex by a fixed site strictly outside the box. -/
def wiredVertexSite (B : ℕ) : FiniteWired.Vertex B → Site 2
  | none => fun i => if i = 0 then (B : ℤ) + 1 else 0
  | some v => FiniteWired.site v

/-- The site representing the wired vertex lies outside the box. -/
theorem wiredVertexSite_none_not_inBox (B : ℕ) :
    ¬FiniteWired.inBox B (wiredVertexSite B none) := by
  intro h
  have h0 := (h 0).2
  simp only [wiredVertexSite, ↓reduceIte] at h0
  omega

/-- The projection to the wired box is a left inverse of its site embedding. -/
theorem wiredSite_wiredVertexSite (B : ℕ) (v : FiniteWired.Vertex B) :
    wiredSite B (wiredVertexSite B v) = v := by
  cases v with
  | none =>
    rw [wiredSite, dif_neg (wiredVertexSite_none_not_inBox B)]
  | some v =>
    have hv : FiniteWired.inBox B (FiniteWired.site v) := fun i => (v i).property
    simp only [wiredVertexSite, wiredSite, dif_pos hv]
    congr 1

/-- The embedding of the finite wired vertex type into lattice sites is injective. -/
theorem wiredVertexSite_injective (B : ℕ) : Function.Injective (wiredVertexSite B) :=
  Function.LeftInverse.injective (wiredSite_wiredVertexSite B)

/-- Every site inside the box is unchanged by projection followed by embedding. -/
theorem wiredVertexSite_wiredSite (B : ℕ) (x : Site 2) (hx : FiniteWired.inBox B x) :
    wiredVertexSite B (wiredSite B x) = x := by
  simp only [wiredSite, dif_pos hx, wiredVertexSite, FiniteWired.site_activeOfSite]

/-- If a lattice step remains inside the box, the wired step has the same endpoint. -/
theorem wiredHead_wiredSite_of_inBox (B : ℕ) (x : Site 2) (d : FiniteWired.Direction)
    (hx : FiniteWired.inBox B x) :
    wiredHead B (wiredSite B x) d = wiredSite B (x + FiniteWired.step d) := by
  simp only [wiredSite, dif_pos hx, wiredHead, FiniteWired.site_activeOfSite]

/-- While a lattice walk remains in a box, the walk with the same increments
on the wired graph is its pointwise projection. -/
theorem wiredWordState_eq_of_confined (B : ℕ) (x : Site 2) (w : WalkDriver)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (hbox : ∀ i ≤ n, FiniteWired.inBox B (position x w i)) :
    ∀ i ≤ n, (wordState (wiredHead B) (wiredSite B x) k w i).1 =
      wiredSite B (position x w i) := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    have hp := ih (Nat.le_trans (Nat.le_succ i) hi)
    change wiredHead B (wordState (wiredHead B) (wiredSite B x) k w i).1 (w i) =
      wiredSite B (position x w (i + 1))
    rw [hp, wiredHead_wiredSite_of_inBox B _ _ (hbox i (Nat.le_trans (Nat.le_succ i) hi)),
      position_succ]

/-- A confined wired direction word has exactly the lattice loop-erased
vertices after applying the embedding of the wired vertex type. -/
theorem wiredWordTrace_loopErase_of_confined (B : ℕ) (x : Site 2) (w : WalkDriver)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (hbox : ∀ i ≤ n, FiniteWired.inBox B (position x w i)) :
    letI : Quiver (FiniteWired.Vertex B) := instructionQuiver (wiredHead B)
    ((loopErase (wordTrace (wiredHead B) (wiredSite B x) w n).2).vertices.map
      (wiredVertexSite B)) = walkErase x w n := by
  letI : Quiver (FiniteWired.Vertex B) := instructionQuiver (wiredHead B)
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  have h := wordTrace_loopErase_map_eq (wiredHead B) latticeDirectionHead
    (wiredVertexSite B) (wiredVertexSite_injective B) (wiredSite B x) x w n ?_
  · rw [wordTrace_lattice_loopErase_vertices x w n] at h
    exact h
  · intro i hi
    rw [wordTrace_fst_eq_wordState (wiredHead B) (wiredSite B x) k w,
      wiredWordState_eq_of_confined B x w k n hbox i hi,
      wiredVertexSite_wiredSite B _ (hbox i hi), wordTrace_lattice_position]

end
end FiniteAvalanches.Wilson.Lattice
