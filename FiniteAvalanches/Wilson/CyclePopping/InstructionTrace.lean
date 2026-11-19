import FiniteAvalanches.Wilson.CyclePopping.Erasure

/-! Chronological stack exploration for endpoint-valued instructions. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-- Each instruction is retained as an arrow to its specified endpoint. -/
@[reducible] def instructionQuiver (head : (v : V) → A v → V) : Quiver V where
  Hom v w := {a : A v // head v a = w}

/-- An instruction stack viewed as a stack of endpoint-indexed arrows. -/
def instructionArrowStacks (head : (v : V) → A v → V) (σ : Stacks A) :
    letI : Quiver V := instructionQuiver head
    ArrowStacks (V := V) :=
  fun v i => ⟨head v (σ v i), ⟨σ v i, rfl⟩⟩

/-- Read the actual instructions along a walk, consuming every departure in order. -/
def instructionTrace (head : (v : V) → A v → V) (σ : Stacks A)
    (k : Cursor V) (x : V) :
    letI : Quiver V := instructionQuiver head
    ℕ → Σ y : V, Path x y := by
  letI : Quiver V := instructionQuiver head
  intro n
  induction n with
  | zero => exact ⟨x, .nil⟩
  | succ n t =>
    let v := t.1
    let a := σ v (consume k t.2 v)
    exact ⟨head v a, t.2.cons ⟨a, rfl⟩⟩

/-- The chronological trace reads precisely the stack entries it consumes. -/
theorem instructionTrace_reads (head : (v : V) → A v → V) (σ : Stacks A)
    (k : Cursor V) (x : V) :
    letI : Quiver V := instructionQuiver head
    ∀ n, reads (instructionArrowStacks head σ) k (instructionTrace head σ k x n).2 := by
  letI : Quiver V := instructionQuiver head
  intro n
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih, rfl⟩


/-- The departures of a trace are the successive positions before its endpoint. -/
theorem instructionTrace_departures (head : (v : V) → A v → V) (σ : Stacks A)
    (k : Cursor V) (x : V) :
    letI : Quiver V := instructionQuiver head
    ∀ n, departures (instructionTrace head σ k x n).2 =
      (List.range n).map (fun i => (instructionTrace head σ k x i).1) := by
  letI : Quiver V := instructionQuiver head
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change departures ((instructionTrace head σ k x n).2.cons _) = _
    rw [departures_cons, ih, List.range_succ, List.map_append]
    rfl

/-- Before its first visit to the roots, every departure of the trace is a nonroot. -/
theorem instructionTrace_departures_avoid (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k : Cursor V) (x : V) :
    letI : Quiver V := instructionQuiver head
    ∀ n, (∀ i < n, (instructionTrace head σ k x i).1 ∉ R) →
      ∀ v ∈ departures (instructionTrace head σ k x n).2, v ∉ R := by
  letI : Quiver V := instructionQuiver head
  intro n hn v hv
  rw [instructionTrace_departures head σ k x n] at hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  exact hn i (List.mem_range.mp hi)

/-- Erasing a finite instruction trace avoiding the roots gives a legal pop run
and selects exactly the retained original instructions. -/
theorem instructionTrace_erasure (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k : Cursor V) (x : V) :
    letI : Quiver V := instructionQuiver head
    ∀ n, (∀ v ∈ departures (instructionTrace head σ k x n).2, v ∉ R) →
      Relation.ReflTransGen (pop_step R head σ) k
        (erasedCursor k (instructionTrace head σ k x n).2) ∧
      selected (instructionArrowStacks head σ)
        (erasedCursor k (instructionTrace head σ k x n).2)
        (loopErase (instructionTrace head σ k x n).2) ∧
      consume (erasedCursor k (instructionTrace head σ k x n).2)
          (loopErase (instructionTrace head σ k x n).2) =
        consume k (instructionTrace head σ k x n).2 := by
  letI : Quiver V := instructionQuiver head
  intro n hn
  have h := loop_erase_cursor_spec R (instructionArrowStacks head σ) k
    (instructionTrace head σ k x n).2 (instructionTrace_reads head σ k x n) hn
  exact h


/-- A stack trace which hits the roots has a first hit whose chronological
loop erasure is realized by legal cycle pops. -/
theorem instructionTrace_firstHit_erasure (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k : Cursor V) (x : V) :
    letI : Quiver V := instructionQuiver head
    (∃ n, (instructionTrace head σ k x n).1 ∈ R) →
    ∃ n, (instructionTrace head σ k x n).1 ∈ R ∧
      (∀ i < n, (instructionTrace head σ k x i).1 ∉ R) ∧
      Relation.ReflTransGen (pop_step R head σ) k
        (erasedCursor k (instructionTrace head σ k x n).2) ∧
      selected (instructionArrowStacks head σ)
        (erasedCursor k (instructionTrace head σ k x n).2)
        (loopErase (instructionTrace head σ k x n).2) ∧
      consume (erasedCursor k (instructionTrace head σ k x n).2)
          (loopErase (instructionTrace head σ k x n).2) =
        consume k (instructionTrace head σ k x n).2 := by
  letI : Quiver V := instructionQuiver head
  intro h
  refine ⟨Nat.find h, Nat.find_spec h, ?_, ?_⟩
  · intro i hi
    exact Nat.find_min h hi
  · apply instructionTrace_erasure R head σ k x
    exact instructionTrace_departures_avoid R head σ k x (Nat.find h)
      (fun i hi => Nat.find_min h hi)

end
end FiniteAvalanches.Wilson.CyclePopping
