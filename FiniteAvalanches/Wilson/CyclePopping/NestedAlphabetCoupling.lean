import FiniteAvalanches.Wilson.CyclePopping.StackAlphabetCoupling
import FiniteAvalanches.Wilson.CyclePopping.RootSetCoupling

/-! Nested-root safety across matching stack instruction alphabets. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V] {A B : V → Type*}

/-- Matching successor stacks have identical first-hit times, endpoints,
loop-erased vertices and pop cursors at a fixed root set. -/
theorem instructionTrace_firstHit_agree
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (S : Set V) (k : Cursor V) (x : V)
    (hstack : ∀ v ∉ S, ∀ i, headA v (σ v i) = headB v (τ v i))
    (hA : ∃ n, (instructionTrace headA σ k x n).1 ∈ S) :
    ∃ hB : ∃ n, (instructionTrace headB τ k x n).1 ∈ S,
      Nat.find hA = Nat.find hB ∧
      (instructionTrace headA σ k x (Nat.find hA)).1 =
        (instructionTrace headB τ k x (Nat.find hB)).1 ∧
      instructionTraceErasedVertices headA σ k x (Nat.find hA) =
        instructionTraceErasedVertices headB τ k x (Nat.find hB) ∧
      instructionTraceErasedCursor headA σ k x (Nat.find hA) =
        instructionTraceErasedCursor headB τ k x (Nat.find hB) := by
  let t := Nat.find hA
  have hav : ∀ i < t, (instructionTrace headA σ k x i).1 ∉ S :=
    fun i hi => Nat.find_min hA hi
  have ht := instructionTrace_agree_until_roots headA headB σ τ S k x t hstack hav
  have hB : ∃ n, (instructionTrace headB τ k x n).1 ∈ S :=
    ⟨t, ht.1 ▸ Nat.find_spec hA⟩
  have htime : Nat.find hB = t := by
    apply Nat.le_antisymm (Nat.find_min' hB (ht.1 ▸ Nat.find_spec hA))
    apply Nat.le_of_not_gt
    intro hlt
    have hp := (instructionTrace_agree_until_roots headA headB σ τ S k x
      (Nat.find hB) hstack (fun i hi => hav i (lt_trans hi hlt))).1
    exact hav (Nat.find hB) hlt (hp.symm ▸ Nat.find_spec hB)
  have herase := instructionTrace_erasure_agree_until_roots headA headB σ τ S k x t hstack hav
  refine ⟨hB, htime.symm, ?_, ?_, ?_⟩ <;> rw [htime]
  · exact ht.1
  · exact herase.1
  · exact herase.2

/-- Nested-root safety transfers between stack systems whose successors agree
away from the larger initial root set. -/
theorem nestedRootSafe_of_matching_successors
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (R S : Set V) (k : Cursor V) (L : List V)
    (hstack : ∀ v ∉ S, ∀ i, headA v (σ v i) = headB v (τ v i))
    (hsafe : nestedRootSafe headA σ R S k L) : nestedRootSafe headB τ R S k L := by
  induction L generalizing R S k with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨hA, hfirst, htail⟩ := hsafe
    obtain ⟨hB, htime, hpoint, hvertices, hcursor⟩ :=
      instructionTrace_firstHit_agree headA headB σ τ S k x hstack hA
    refine ⟨hB, hpoint ▸ hfirst, ?_⟩
    change nestedRootSafe headA σ
      (R ∪ {v | v ∈ instructionTraceErasedVertices headA σ k x (Nat.find hA)})
      (S ∪ {v | v ∈ instructionTraceErasedVertices headA σ k x (Nat.find hA)})
      (instructionTraceErasedCursor headA σ k x (Nat.find hA)) xs at htail
    change nestedRootSafe headB τ
      (R ∪ {v | v ∈ instructionTraceErasedVertices headB τ k x (Nat.find hB)})
      (S ∪ {v | v ∈ instructionTraceErasedVertices headB τ k x (Nat.find hB)})
      (instructionTraceErasedCursor headB τ k x (Nat.find hB)) xs
    rw [← hvertices, ← hcursor]
    apply ih _ _ _ ?_ htail
    intro v hv i
    exact hstack v (fun hS => hv (Or.inl hS)) i

end
end FiniteAvalanches.Wilson.CyclePopping
