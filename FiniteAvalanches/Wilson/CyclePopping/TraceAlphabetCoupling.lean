import FiniteAvalanches.Wilson.CyclePopping.InstructionTrace
import FiniteAvalanches.Wilson.CyclePopping.ErasureNaturality

/-! Stack traces with different instruction alphabets and the same successors. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V] {A B : V → Type*}

/-- The visited vertex list of an instruction trace. -/
def instructionTraceVertices (head : (v : V) → A v → V) (σ : Stacks A)
    (k : Cursor V) (x : V) (n : ℕ) : List V :=
  letI : Quiver V := instructionQuiver head
  (instructionTrace head σ k x n).2.vertices

/-- The consumed stack cursor of an instruction trace. -/
def instructionTraceCursor (head : (v : V) → A v → V) (σ : Stacks A)
    (k : Cursor V) (x : V) (n : ℕ) : Cursor V :=
  letI : Quiver V := instructionQuiver head
  consume k (instructionTrace head σ k x n).2

/-- A trace appends its next position and increments the departure cursor. -/
theorem instructionTrace_next (head : (v : V) → A v → V) (σ : Stacks A)
    (k : Cursor V) (x : V) (n : ℕ) :
    let v := (instructionTrace head σ k x n).1
    (instructionTrace head σ k x (n + 1)).1 =
        head v (σ v (instructionTraceCursor head σ k x n v)) ∧
    instructionTraceCursor head σ k x (n + 1) =
        pop (instructionTraceCursor head σ k x n) {v} ∧
    instructionTraceVertices head σ k x (n + 1) =
      instructionTraceVertices head σ k x n ++ [(instructionTrace head σ k x (n + 1)).1] := by
  constructor
  · rfl
  constructor
  · rfl
  · simp only [instructionTraceVertices, instructionTrace, Path.vertices_cons, List.concat_eq_append]

/-- Matching successor stacks give the same positions, consumed cursors and
vertex words until the first visit to a distinguished set. -/
theorem instructionTrace_agree_until_roots
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (R : Set V) (k : Cursor V) (x : V) (n : ℕ)
    (hstack : ∀ v ∉ R, ∀ i, headA v (σ v i) = headB v (τ v i))
    (havoid : ∀ i < n, (instructionTrace headA σ k x i).1 ∉ R) :
    (instructionTrace headA σ k x n).1 = (instructionTrace headB τ k x n).1 ∧
      instructionTraceCursor headA σ k x n = instructionTraceCursor headB τ k x n ∧
      instructionTraceVertices headA σ k x n = instructionTraceVertices headB τ k x n := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hp, hc, hv⟩ := ih (fun i hi => havoid i (Nat.lt_succ_of_lt hi))
    have hnot := havoid n (Nat.lt_succ_self n)
    have ha := instructionTrace_next headA σ k x n
    have hb := instructionTrace_next headB τ k x n
    have hp' : (instructionTrace headA σ k x (n + 1)).1 =
        (instructionTrace headB τ k x (n + 1)).1 := by
      rw [ha.1, hb.1, ← hp, ← hc]
      exact hstack _ hnot _
    have hc' : instructionTraceCursor headA σ k x (n + 1) =
        instructionTraceCursor headB τ k x (n + 1) := by
      rw [ha.2.1, hb.2.1, hp, hc]
    refine ⟨hp', hc', ?_⟩
    rw [ha.2.2, hb.2.2, hp', hv]

/-- The retained vertex word after chronologically erasing a stack trace. -/
def instructionTraceErasedVertices (head : (v : V) → A v → V) (σ : Stacks A)
    (k : Cursor V) (x : V) (n : ℕ) : List V :=
  letI : Quiver V := instructionQuiver head
  (loopErase (instructionTrace head σ k x n).2).vertices

/-- The cycle-pop cursor induced by the erasure of a stack trace. -/
def instructionTraceErasedCursor (head : (v : V) → A v → V) (σ : Stacks A)
    (k : Cursor V) (x : V) (n : ℕ) : Cursor V :=
  letI : Quiver V := instructionQuiver head
  erasedCursor k (instructionTrace head σ k x n).2

/-- Erased trace vertices depend only on the chronological vertex word. -/
theorem instructionTraceErasedVertices_eq_fold (head : (v : V) → A v → V)
    (σ : Stacks A) (k : Cursor V) (x : V) (n : ℕ) :
    instructionTraceErasedVertices head σ k x n =
      (instructionTraceVertices head σ k x n).foldl eraseVertex [] := by
  letI : Quiver V := instructionQuiver head
  exact loopErase_vertices_fold (instructionTrace head σ k x n).2

/-- Erased cursors depend on raw consumption and the retained vertex word. -/
theorem instructionTraceErasedCursor_eq (head : (v : V) → A v → V)
    (σ : Stacks A) (k : Cursor V) (x : V) (n : ℕ) :
    instructionTraceErasedCursor head σ k x n = fun v =>
      instructionTraceCursor head σ k x n v -
        (instructionTraceErasedVertices head σ k x n).dropLast.count v := rfl

/-- Two traces with matching successors have identical erased vertices and
cycle-pop cursors until the first visit to the distinguished roots. -/
theorem instructionTrace_erasure_agree_until_roots
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (R : Set V) (k : Cursor V) (x : V) (n : ℕ)
    (hstack : ∀ v ∉ R, ∀ i, headA v (σ v i) = headB v (τ v i))
    (havoid : ∀ i < n, (instructionTrace headA σ k x i).1 ∉ R) :
    instructionTraceErasedVertices headA σ k x n =
        instructionTraceErasedVertices headB τ k x n ∧
      instructionTraceErasedCursor headA σ k x n =
        instructionTraceErasedCursor headB τ k x n := by
  obtain ⟨_, hc, hv⟩ := instructionTrace_agree_until_roots headA headB σ τ R k x n hstack havoid
  have he : instructionTraceErasedVertices headA σ k x n =
      instructionTraceErasedVertices headB τ k x n := by
    rw [instructionTraceErasedVertices_eq_fold, instructionTraceErasedVertices_eq_fold, hv]
  refine ⟨he, ?_⟩
  rw [instructionTraceErasedCursor_eq, instructionTraceErasedCursor_eq, hc, he]

end
end FiniteAvalanches.Wilson.CyclePopping
