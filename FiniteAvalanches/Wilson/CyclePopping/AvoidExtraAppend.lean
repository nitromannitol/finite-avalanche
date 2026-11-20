import FiniteAvalanches.Wilson.CyclePopping.AvoidExtraRoots

/-! Concatenating Wilson explorations that avoid extra roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V] {A : V → Type*}

/-- Two consecutive finite explorations avoid the designated extra roots when
each of the two parts does. -/
theorem stackExploreAvoidsRoots_append (head : (v : V) → A v → V) (σ : Stacks A)
    (D R : Set V) (k : Cursor V) (L M : List V) (S : Set V) (l : Cursor V)
    (hbefore : stackExploreAvoidsRoots head σ D R k L)
    (hs : stackExplore head σ R k L = some (S, l))
    (hafter : stackExploreAvoidsRoots head σ D S l M) :
    stackExploreAvoidsRoots head σ D R k (L ++ M) := by
  induction L generalizing R k with
  | nil =>
    simp only [stackExplore, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact hafter
  | cons x xs ih =>
    obtain ⟨hR, hfirst, htail⟩ := hbefore
    letI : Quiver V := instructionQuiver head
    let p := loopErase (instructionTrace head σ k x (Nat.find hR)).2
    let U : Set V := {v | v ∈ p.vertices}
    let j := erasedCursor k (instructionTrace head σ k x (Nat.find hR)).2
    have hstep : stackStep head σ R k x = some (R ∪ U, j) := by
      simp only [stackStep, dif_pos hR, U, p, j]
    have hrun : stackExplore head σ (R ∪ U) j xs = some (S, l) := by
      simpa only [stackExplore, hstep, Option.bind_some] using hs
    refine ⟨hR, hfirst, ?_⟩
    change stackExploreAvoidsRoots head σ D (R ∪ U) j (xs ++ M)
    exact ih (R ∪ U) j htail hrun

end
end FiniteAvalanches.Wilson.CyclePopping
