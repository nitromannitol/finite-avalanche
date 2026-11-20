import FiniteAvalanches.Wilson.CyclePopping.TraceAlphabetCoupling
import FiniteAvalanches.Wilson.CyclePopping.StackExploration

/-! Wilson explorations agree across matching instruction alphabets. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V] {A B : V → Type*}

/-- Matching successor stacks away from the roots give the same first-hit
Wilson step, including the retained roots and erased cursor. -/
theorem stackStep_eq_of_matching_successors
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (R : Set V) (k : Cursor V) (x : V)
    (hstack : ∀ v ∉ R, ∀ i, headA v (σ v i) = headB v (τ v i)) :
    stackStep headA σ R k x = stackStep headB τ R k x := by
  by_cases hA : ∃ n, (instructionTrace headA σ k x n).1 ∈ R
  · let t := Nat.find hA
    have hav : ∀ i < t, (instructionTrace headA σ k x i).1 ∉ R :=
      fun i hi => Nat.find_min hA hi
    have ht := instructionTrace_agree_until_roots headA headB σ τ R k x t hstack hav
    have hB : ∃ n, (instructionTrace headB τ k x n).1 ∈ R :=
      ⟨t, ht.1 ▸ Nat.find_spec hA⟩
    have htime : Nat.find hB = t := by
      apply Nat.le_antisymm (Nat.find_min' hB (ht.1 ▸ Nat.find_spec hA))
      apply Nat.le_of_not_gt
      intro hlt
      have hp := (instructionTrace_agree_until_roots headA headB σ τ R k x
        (Nat.find hB) hstack (fun i hi => hav i (lt_trans hi hlt))).1
      exact hav (Nat.find hB) hlt (hp.symm ▸ Nat.find_spec hB)
    have herase := instructionTrace_erasure_agree_until_roots headA headB σ τ R k x t hstack hav
    simp only [stackStep, dif_pos hA, dif_pos hB]
    change some (R ∪ {v | v ∈ instructionTraceErasedVertices headA σ k x t},
      instructionTraceErasedCursor headA σ k x t) =
      some (R ∪ {v | v ∈ instructionTraceErasedVertices headB τ k x (Nat.find hB)},
      instructionTraceErasedCursor headB τ k x (Nat.find hB))
    rw [htime, herase.1, herase.2]
  · have hB : ¬∃ n, (instructionTrace headB τ k x n).1 ∈ R := by
      intro h
      let t := Nat.find h
      have hav : ∀ i < t, (instructionTrace headA σ k x i).1 ∉ R :=
        fun i hi hr => hA ⟨i, hr⟩
      have ht := instructionTrace_agree_until_roots headA headB σ τ R k x t hstack hav
      exact hA ⟨t, ht.1.symm ▸ Nat.find_spec h⟩
    simp only [stackStep, dif_neg hA, dif_neg hB]

/-- Matching successor stacks produce the same finite ordered Wilson
exploration when the roots may only grow. -/
theorem stackExplore_eq_of_matching_successors
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (R : Set V) (k : Cursor V) (L : List V)
    (hstack : ∀ v ∉ R, ∀ i, headA v (σ v i) = headB v (τ v i)) :
    stackExplore headA σ R k L = stackExplore headB τ R k L := by
  induction L generalizing R k with
  | nil => rfl
  | cons x xs ih =>
    have he := stackStep_eq_of_matching_successors headA headB σ τ R k x hstack
    cases hs : stackStep headB τ R k x with
    | none => simp only [stackExplore, he, hs, Option.bind_none]
    | some out =>
      obtain ⟨S, l⟩ := out
      have hRS := (stackStep_of_some R headB τ k x S l hs).1
      have hm : ∀ v ∉ S, ∀ i, headA v (σ v i) = headB v (τ v i) :=
        fun v hv => hstack v (fun hR => hv (hRS hR))
      simpa only [stackExplore, he, hs, Option.bind_some] using ih S l hm

end
end FiniteAvalanches.Wilson.CyclePopping
