import FiniteAvalanches.Wilson.CyclePopping.ErasureNaturality
import FiniteAvalanches.Wilson.CyclePopping.WordTrace

/-! Finite word traces and loop erasures under compatible vertex relabelings. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V W D : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
/-- A word trace lists its successive positions in chronological order. -/
theorem wordTrace_vertices (head : V → D → V) (x : V) (w : ℕ → D) :
    letI : Quiver V := instructionQuiver head
    ∀ n, (wordTrace head x w n).2.vertices =
      (List.range (n + 1)).map (fun i => (wordTrace head x w i).1) := by
  letI : Quiver V := instructionQuiver head
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((wordTrace head x w n).2.cons _).vertices = _
    rw [Path.vertices_cons, List.concat_eq_append, ih]
    rw [show List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] from List.range_succ,
      List.map_append]
    rfl

/-- Positions of a word trace agree with the position component of the
corresponding word-driven state, regardless of the initial cursor. -/
theorem wordTrace_fst_eq_wordState (head : V → D → V) (x : V)
    (k : Cursor V) (w : ℕ → D) :
    letI : Quiver V := instructionQuiver head
    ∀ n, (wordTrace head x w n).1 = (wordState head x k w n).1 := by
  letI : Quiver V := instructionQuiver head
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change head (wordTrace head x w n).1 (w n) = head (wordState head x k w n).1 (w n)
    rw [ih]

/-- Compatible positions imply compatible loop erasures of the finite words. -/
theorem wordTrace_loopErase_map_eq (head : V → D → V) (head' : W → D → W)
    (f : V → W) (hf : Function.Injective f) (x : V) (y : W) (w : ℕ → D) (n : ℕ)
    (h : ∀ i ≤ n, f ((wordTrace head x w i).1) = (wordTrace head' y w i).1) :
    letI : Quiver V := instructionQuiver head
    letI : Quiver W := instructionQuiver head'
    (loopErase (wordTrace head x w n).2).vertices.map f =
      (loopErase (wordTrace head' y w n).2).vertices := by
  letI : Quiver V := instructionQuiver head
  letI : Quiver W := instructionQuiver head'
  apply loopErase_vertices_map_eq f hf
  rw [wordTrace_vertices, wordTrace_vertices, List.map_map]
  apply List.map_congr_left
  intro i hi
  exact h i (Nat.le_of_lt_succ (List.mem_range.mp hi))

/-- When the step functions commute along a finite word, all positions of
that word commute with the vertex map. -/
theorem wordState_map_fst_of_steps (head : V → D → V) (head' : W → D → W)
    (f : V → W) (x : V) (y : W) (k : Cursor V) (l : Cursor W)
    (w : ℕ → D) (n : ℕ) (hstart : f x = y)
    (hstep : ∀ i < n, f (head (wordState head x k w i).1 (w i)) =
      head' (f (wordState head x k w i).1) (w i)) :
    ∀ i ≤ n, f (wordState head x k w i).1 = (wordState head' y l w i).1 := by
  intro i hi
  induction i with
  | zero => exact hstart
  | succ i ih =>
    have hprev := ih (Nat.le_trans (Nat.le_succ i) hi)
    change f (head (wordState head x k w i).1 (w i)) =
      head' (wordState head' y l w i).1 (w i)
    rw [hstep i (lt_of_lt_of_le (Nat.lt_succ_self i) hi), hprev]

/-- Compatible finite word states yield compatible loop-erased vertex lists. -/
theorem wordTrace_loopErase_map_of_steps (head : V → D → V) (head' : W → D → W)
    (f : V → W) (hf : Function.Injective f) (x : V) (y : W)
    (k : Cursor V) (l : Cursor W) (w : ℕ → D) (n : ℕ) (hstart : f x = y)
    (hstep : ∀ i < n, f (head (wordState head x k w i).1 (w i)) =
      head' (f (wordState head x k w i).1) (w i)) :
    letI : Quiver V := instructionQuiver head
    letI : Quiver W := instructionQuiver head'
    (loopErase (wordTrace head x w n).2).vertices.map f =
      (loopErase (wordTrace head' y w n).2).vertices := by
  apply wordTrace_loopErase_map_eq head head' f hf x y w n
  intro i hi
  rw [wordTrace_fst_eq_wordState head x k w, wordTrace_fst_eq_wordState head' y l w]
  exact wordState_map_fst_of_steps head head' f x y k l w n hstart hstep i hi

end
end FiniteAvalanches.Wilson.CyclePopping
