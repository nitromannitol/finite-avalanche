import FiniteAvalanches.Wilson.CyclePopping.StackAlphabetCoupling

/-! Cycle-popping runs agree across instruction alphabets with matching successors. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V] {A B : V → Type*}

/-- Matching successors away from the roots give the same legal cycles. -/
theorem isCycle_iff_of_matching_successors (R : Set V)
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (k : Cursor V) (c : Finset V)
    (hstack : ∀ v ∉ R, ∀ i, headA v (σ v i) = headB v (τ v i)) :
    IsCycle R (next headA σ k) c ↔ IsCycle R (next headB τ k) c := by
  constructor
  · intro h
    apply h.congr
    intro v hv
    exact hstack v (h.avoids_roots v hv) (k v)
  · intro h
    apply h.congr
    intro v hv
    exact (hstack v (h.avoids_roots v hv) (k v)).symm

/-- Matching successors away from the roots give the same legal pop steps. -/
theorem pop_step_iff_of_matching_successors (R : Set V)
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (k l : Cursor V)
    (hstack : ∀ v ∉ R, ∀ i, headA v (σ v i) = headB v (τ v i)) :
    pop_step R headA σ k l ↔ pop_step R headB τ k l := by
  simp only [pop_step]
  exact exists_congr fun c =>
    and_congr (isCycle_iff_of_matching_successors R headA headB σ τ k c hstack) Iff.rfl

/-- Matching successors away from the roots give the same finite legal runs. -/
theorem pop_run_iff_of_matching_successors (R : Set V)
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (k l : Cursor V)
    (hstack : ∀ v ∉ R, ∀ i, headA v (σ v i) = headB v (τ v i)) :
    Relation.ReflTransGen (pop_step R headA σ) k l ↔
      Relation.ReflTransGen (pop_step R headB τ) k l := by
  constructor <;> intro h
  · exact Relation.ReflTransGen.mono
      (fun _ _ hs => (pop_step_iff_of_matching_successors R headA headB σ τ _ _ hstack).mp hs) k l h
  · exact Relation.ReflTransGen.mono
      (fun _ _ hs => (pop_step_iff_of_matching_successors R headA headB σ τ _ _ hstack).mpr hs) k l h

/-- Matching successors away from the roots give the same terminal cursors. -/
theorem terminal_iff_of_matching_successors (R : Set V)
    (headA : (v : V) → A v → V) (headB : (v : V) → B v → V)
    (σ : Stacks A) (τ : Stacks B) (k : Cursor V)
    (hstack : ∀ v ∉ R, ∀ i, headA v (σ v i) = headB v (τ v i)) :
    terminal R headA σ k ↔ terminal R headB τ k := by
  constructor <;> intro h c hc
  · exact h c ((isCycle_iff_of_matching_successors R headA headB σ τ k c hstack).mpr hc)
  · exact h c ((isCycle_iff_of_matching_successors R headA headB σ τ k c hstack).mp hc)

end
end FiniteAvalanches.Wilson.CyclePopping
