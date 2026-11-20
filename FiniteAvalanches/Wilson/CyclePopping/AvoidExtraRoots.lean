import FiniteAvalanches.Wilson.CyclePopping.RootSetCoupling

/-! Avoiding extra roots during a finite Wilson exploration. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V] {A : V → Type*}

/-- Every branch in an exploration first hits an attached root outside a
specified set of extra roots. -/
def stackExploreAvoidsRoots (head : (v : V) → A v → V) (σ : Stacks A) (D : Set V) :
    Set V → Cursor V → List V → Prop
  | _, _, [] => True
  | S, k, x :: xs =>
    ∃ hS : ∃ n, (instructionTrace head σ k x n).1 ∈ S,
      (instructionTrace head σ k x (Nat.find hS)).1 ∉ D ∧
      letI : Quiver V := instructionQuiver head
      let p := loopErase (instructionTrace head σ k x (Nat.find hS)).2
      let U : Set V := {v | v ∈ p.vertices}
      let l := erasedCursor k (instructionTrace head σ k x (Nat.find hS)).2
      stackExploreAvoidsRoots head σ D (S ∪ U) l xs

/-- Avoiding the extra initial roots makes nested-root exploration safe. -/
theorem nestedRootSafe_of_avoidsRoots (head : (v : V) → A v → V) (σ : Stacks A)
    (R S D : Set V) (k : Cursor V) (L : List V)
    (hSD : S ⊆ R ∪ D) (havoid : stackExploreAvoidsRoots head σ D S k L) :
    nestedRootSafe head σ R S k L := by
  induction L generalizing R S k with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨hS, hnot, htail⟩ := havoid
    have hfirst : (instructionTrace head σ k x (Nat.find hS)).1 ∈ R :=
      (hSD (Nat.find_spec hS)).resolve_right hnot
    refine ⟨hS, hfirst, ?_⟩
    letI : Quiver V := instructionQuiver head
    let p := loopErase (instructionTrace head σ k x (Nat.find hS)).2
    let U : Set V := {v | v ∈ p.vertices}
    let l := erasedCursor k (instructionTrace head σ k x (Nat.find hS)).2
    change stackExploreAvoidsRoots head σ D (S ∪ U) l xs at htail
    change nestedRootSafe head σ (R ∪ U) (S ∪ U) l xs
    apply ih (R ∪ U) (S ∪ U) l ?_ htail
    intro v hv
    rcases hv with hv | hv
    · rcases hSD hv with hv | hv
      · exact Or.inl (Or.inl hv)
      · exact Or.inr hv
    · exact Or.inl (Or.inr hv)

/-- If all larger-root first hits avoid the extra roots, the smaller and larger
explorations attach the same branches and have the same pop cursor. -/
theorem stackExplore_eq_of_avoidsExtraRoots (head : (v : V) → A v → V) (σ : Stacks A)
    (R S D : Set V) (k : Cursor V) (L : List V)
    (hRS : R ⊆ S) (hSD : S ⊆ R ∪ D)
    (havoid : stackExploreAvoidsRoots head σ D S k L) :
    ∃ T l, stackExplore head σ R k L = some (T, l) ∧
      stackExplore head σ S k L = some (S ∪ T, l) ∧ R ⊆ T :=
  stackExplore_eq_of_nestedRootSafe head σ R S k L hRS
    (nestedRootSafe_of_avoidsRoots head σ R S D k L hSD havoid)

end
end FiniteAvalanches.Wilson.CyclePopping
