import FiniteAvalanches.Wilson.CyclePopping.ReadingRoots
import FiniteAvalanches.Wilson.CyclePopping.TraceReading

/-! Chronological stack traces are insensitive to cursor changes on roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V D : Type*} [DecidableEq V]

/-- If two cursors agree outside the roots, their instruction traces agree up
to any time whose earlier positions avoid the roots. -/
theorem instructionTrace_eq_until_roots (head : V → D → V) (R : Set V) (x : V)
    (k l : Cursor V) (σ : V × ℕ → D) (n : ℕ)
    (hcursor : ∀ v, v ∉ R → k v = l v)
    (havoid : ∀ i < n,
      (instructionTrace head (fun v j => σ (v, j)) k x i).1 ∉ R) :
    instructionTrace head (fun v j => σ (v, j)) k x n =
      instructionTrace head (fun v j => σ (v, j)) l x n := by
  letI : Quiver V := instructionQuiver head
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht := ih (fun i hi => havoid i (Nat.lt_succ_of_lt hi))
    have hv := havoid n (Nat.lt_succ_self n)
    have hc : consume k (instructionTrace head (fun v j => σ (v, j)) k x n).2
        (instructionTrace head (fun v j => σ (v, j)) k x n).1 =
        consume l (instructionTrace head (fun v j => σ (v, j)) l x n).2
          (instructionTrace head (fun v j => σ (v, j)) l x n).1 := by
      rw [← ht, consume_apply, consume_apply, hcursor _ hv]
    change (let q := instructionTrace head (fun v j => σ (v, j)) k x n
      let a := σ (q.1, consume k q.2 q.1)
      (⟨head q.1 a, q.2.cons ⟨a, rfl⟩⟩ : Σ y : V, Path x y)) =
      (let q := instructionTrace head (fun v j => σ (v, j)) l x n
      let a := σ (q.1, consume l q.2 q.1)
      (⟨head q.1 a, q.2.cons ⟨a, rfl⟩⟩ : Σ y : V, Path x y))
    rw [← ht] at hc
    rw [← ht]
    dsimp only
    rw [hc]

end
end FiniteAvalanches.Wilson.CyclePopping
