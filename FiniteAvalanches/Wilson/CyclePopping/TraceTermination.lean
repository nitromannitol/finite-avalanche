import FiniteAvalanches.Wilson.CyclePopping.InstructionTrace
import Mathlib.Data.Finset.Sum

/-! A finite terminal pop configuration forces stack traces to hit the roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [Quiver V]

omit [Quiver V] in
/-- Consuming one departure increases the total cursor by one. -/
theorem sum_pop_singleton (k : Cursor V) (v : V) :
    (∑ x, pop k {v} x) = (∑ x, k x) + 1 := by
  have he : pop k {v} = fun x => k x + if x = v then 1 else 0 := by
    funext x
    by_cases h : x = v <;> simp [pop, h]
  rw [he, Finset.sum_add_distrib]
  simp

/-- The total cursor increase is the length of the consumed path. -/
theorem sum_consume (k : Cursor V) {x y : V} (p : Path x y) :
    (∑ v, consume k p v) = (∑ v, k v) + p.length := by
  induction p with
  | nil => simp [consume]
  | @cons b c p e ih =>
    rw [consume, sum_pop_singleton, ih, Path.length_cons]
    omega

omit [Fintype V] in
/-- Consuming a simple path advances any particular vertex at most once. -/
theorem consume_le_add_one (k : Cursor V) {x y : V} (p : Path x y)
    (hp : p.vertices.Nodup) (v : V) : consume k p v ≤ k v + 1 := by
  rw [consume_of_nodup k p hp]
  by_cases hv : v ∈ (departures p).toFinset
  · rw [pop_apply_of_mem _ _ hv]
  · rw [pop_apply_of_not_mem _ _ hv]
    exact Nat.le_succ _

variable {A : V → Type*}

omit [Fintype V] [Quiver V] in
/-- A stack trace has one arrow per recorded step. -/
theorem instructionTrace_length (head : (v : V) → A v → V) (σ : Stacks A)
    (k : Cursor V) (x : V) :
    letI : Quiver V := instructionQuiver head
    ∀ n, (instructionTrace head σ k x n).2.length = n := by
  letI : Quiver V := instructionQuiver head
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((instructionTrace head σ k x n).2.cons _).length = n + 1
    rw [Path.length_cons, ih]

omit [Quiver V] in
/-- If a finite legal pop run reaches a terminal cursor, every chronological
instruction trace started at the same cursor eventually reaches a root. -/
theorem instructionTrace_hits_of_terminal (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k t : Cursor V)
    (hrun : Relation.ReflTransGen (pop_step R head σ) k t)
    (ht : terminal R head σ t) (x : V) :
    ∃ n, (instructionTrace head σ k x n).1 ∈ R := by
  letI : Quiver V := instructionQuiver head
  by_contra h
  push Not at h
  let n := (∑ v, (t v + 1)) + 1
  have ha : ∀ v ∈ departures (instructionTrace head σ k x n).2, v ∉ R :=
    instructionTrace_departures_avoid R head σ k x n (fun i _ => h i)
  have herase := instructionTrace_erasure R head σ k x n ha
  have hle : erasedCursor k (instructionTrace head σ k x n).2 ≤ t :=
    cursor_le_terminal R head σ hrun herase.1 ht
  have hbound (v : V) : consume k (instructionTrace head σ k x n).2 v ≤ t v + 1 := by
    rw [← herase.2.2]
    exact le_trans (consume_le_add_one _ _ (loopErase_vertices_nodup _) v)
      (Nat.add_le_add_right (hle v) 1)
  have hsum : (∑ v, consume k (instructionTrace head σ k x n).2 v) ≤
      ∑ v, (t v + 1) := Finset.sum_le_sum (fun v _ => hbound v)
  have hcount := sum_consume k (instructionTrace head σ k x n).2
  rw [instructionTrace_length head σ k x n] at hcount
  dsimp [n] at hsum hcount
  omega

end
end FiniteAvalanches.Wilson.CyclePopping
