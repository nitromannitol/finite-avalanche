import FiniteAvalanches.Wilson.CyclePopping.StackExploration

/-! Coupling Wilson steps stopped at nested sets of roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V] {A : V → Type*}

/-- If the first hit of a larger root set is already in a smaller root set,
the two first-hit times agree. -/
theorem firstHit_eq_of_nested_roots (head : (v : V) → A v → V)
    (σ : Stacks A) (k : Cursor V) (x : V) (R S : Set V) (hRS : R ⊆ S)
    (hS : ∃ n, (instructionTrace head σ k x n).1 ∈ S)
    (hfirst : (instructionTrace head σ k x (Nat.find hS)).1 ∈ R) :
    ∃ hR : ∃ n, (instructionTrace head σ k x n).1 ∈ R, Nat.find hR = Nat.find hS := by
  let hR : ∃ n, (instructionTrace head σ k x n).1 ∈ R := ⟨Nat.find hS, hfirst⟩
  refine ⟨hR, Nat.le_antisymm (Nat.find_min' hR hfirst) ?_⟩
  exact Nat.find_min' hS (hRS (Nat.find_spec hR))

/-- Nested-root Wilson steps use the same erased branch and cursor when the
larger-root first hit belongs to the smaller root set. -/
theorem stackStep_eq_of_nested_roots (head : (v : V) → A v → V)
    (σ : Stacks A) (k : Cursor V) (x : V) (R S : Set V) (hRS : R ⊆ S)
    (hS : ∃ n, (instructionTrace head σ k x n).1 ∈ S)
    (hfirst : (instructionTrace head σ k x (Nat.find hS)).1 ∈ R) :
    letI : Quiver V := instructionQuiver head
    let p := loopErase (instructionTrace head σ k x (Nat.find hS)).2
    let U : Set V := {v | v ∈ p.vertices}
    let l := erasedCursor k (instructionTrace head σ k x (Nat.find hS)).2
    stackStep head σ R k x = some (R ∪ U, l) ∧
      stackStep head σ S k x = some (S ∪ U, l) := by
  letI : Quiver V := instructionQuiver head
  obtain ⟨hR, he⟩ := firstHit_eq_of_nested_roots head σ k x R S hRS hS hfirst
  constructor
  · simp only [stackStep, dif_pos hR]
    change some (R ∪ {v | v ∈ (loopErase (instructionTrace head σ k x (Nat.find hR)).2).vertices},
      erasedCursor k (instructionTrace head σ k x (Nat.find hR)).2) = _
    rw [he]
  · simp only [stackStep, dif_pos hS]

/-- A nested-root exploration is safe when every branch stopped at the larger
root set first hits a vertex already attached to the smaller root set. -/
def nestedRootSafe (head : (v : V) → A v → V) (σ : Stacks A) :
    Set V → Set V → Cursor V → List V → Prop
  | _, _, _, [] => True
  | R, S, k, x :: xs =>
    ∃ hS : ∃ n, (instructionTrace head σ k x n).1 ∈ S,
      (instructionTrace head σ k x (Nat.find hS)).1 ∈ R ∧
      letI : Quiver V := instructionQuiver head
      let p := loopErase (instructionTrace head σ k x (Nat.find hS)).2
      let U : Set V := {v | v ∈ p.vertices}
      let l := erasedCursor k (instructionTrace head σ k x (Nat.find hS)).2
      nestedRootSafe head σ (R ∪ U) (S ∪ U) l xs

/-- Safe nested-root explorations attach the same branches and finish with
the same cursor; the larger output only retains its extra initial roots. -/
theorem stackExplore_eq_of_nestedRootSafe (head : (v : V) → A v → V)
    (σ : Stacks A) (R S : Set V) (k : Cursor V) (L : List V)
    (hRS : R ⊆ S) (hsafe : nestedRootSafe head σ R S k L) :
    ∃ T l, stackExplore head σ R k L = some (T, l) ∧
      stackExplore head σ S k L = some (S ∪ T, l) ∧ R ⊆ T := by
  induction L generalizing R S k with
  | nil =>
    refine ⟨R, k, rfl, ?_, Set.Subset.rfl⟩
    simp only [stackExplore, Set.union_eq_left.mpr hRS]
  | cons x xs ih =>
    obtain ⟨hS, hfirst, htail⟩ := hsafe
    letI : Quiver V := instructionQuiver head
    let p := loopErase (instructionTrace head σ k x (Nat.find hS)).2
    let U : Set V := {v | v ∈ p.vertices}
    let j := erasedCursor k (instructionTrace head σ k x (Nat.find hS)).2
    have hs := stackStep_eq_of_nested_roots head σ k x R S hRS hS hfirst
    change stackStep head σ R k x = some (R ∪ U, j) ∧
      stackStep head σ S k x = some (S ∪ U, j) at hs
    have hsub : R ∪ U ⊆ S ∪ U := Set.union_subset_union_left U hRS
    obtain ⟨T, l, hsmall, hlarge, hT⟩ := ih (R ∪ U) (S ∪ U) j hsub htail
    have hUT : U ⊆ T := Set.subset_union_right.trans hT
    have he : (S ∪ U) ∪ T = S ∪ T := by
      ext v
      simp only [Set.mem_union]
      constructor
      · rintro ((hv | hv) | hv)
        · exact Or.inl hv
        · exact Or.inr (hUT hv)
        · exact Or.inr hv
      · rintro (hv | hv)
        · exact Or.inl (Or.inl hv)
        · exact Or.inr hv
    refine ⟨T, l, ?_, ?_, Set.subset_union_left.trans hT⟩
    · simpa only [stackExplore, hs.1, Option.bind_some] using hsmall
    · simpa only [stackExplore, hs.2, Option.bind_some, he] using hlarge

end
end FiniteAvalanches.Wilson.CyclePopping
