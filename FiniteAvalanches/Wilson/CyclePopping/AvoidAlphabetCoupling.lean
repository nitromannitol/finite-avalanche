import FiniteAvalanches.Wilson.CyclePopping.NestedAlphabetCoupling
import FiniteAvalanches.Wilson.CyclePopping.AvoidExtraRoots

/-! Root avoidance across matching instruction alphabets. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V] {A B : V → Type*}

/-- A finite exploration's first-hit endpoints avoid the same extra roots
when the successor stacks agree away from the stopping roots. -/
theorem stackExploreAvoidsRoots_of_matching_successors
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (S D : Set V) (k : Cursor V) (L : List V)
    (hstack : ∀ v ∉ S, ∀ i, headA v (σ v i) = headB v (τ v i))
    (havoid : stackExploreAvoidsRoots headA σ D S k L) :
    stackExploreAvoidsRoots headB τ D S k L := by
  induction L generalizing S k with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨hA, hfirst, htail⟩ := havoid
    obtain ⟨hB, _, hpoint, hvertices, hcursor⟩ :=
      instructionTrace_firstHit_agree headA headB σ τ S k x hstack hA
    refine ⟨hB, hpoint ▸ hfirst, ?_⟩
    change stackExploreAvoidsRoots headA σ D
      (S ∪ {v | v ∈ instructionTraceErasedVertices headA σ k x (Nat.find hA)})
      (instructionTraceErasedCursor headA σ k x (Nat.find hA)) xs at htail
    change stackExploreAvoidsRoots headB τ D
      (S ∪ {v | v ∈ instructionTraceErasedVertices headB τ k x (Nat.find hB)})
      (instructionTraceErasedCursor headB τ k x (Nat.find hB)) xs
    rw [← hvertices, ← hcursor]
    apply ih _ _ ?_ htail
    intro v hv i
    exact hstack v (fun hS => hv (Or.inl hS)) i

end
end FiniteAvalanches.Wilson.CyclePopping
