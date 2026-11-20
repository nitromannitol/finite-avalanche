import FiniteAvalanches.Wilson.CyclePopping.TraceRoots
import FiniteAvalanches.Wilson.CyclePopping.StackExploration

/-! Wilson stack steps with a cursor recording all raw departures. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V D : Type*} [DecidableEq V]

/-- Attach the loop-erased branch while recording every raw stack departure. -/
def rawStackStep (head : V → D → V) (σ : V × ℕ → D)
    (R : Set V) (k : Cursor V) (x : V) : Option (Set V × Cursor V) := by
  letI : Quiver V := instructionQuiver head
  exact if h : ∃ n, (instructionTrace head (fun v j => σ (v, j)) k x n).1 ∈ R then
    let p := (instructionTrace head (fun v j => σ (v, j)) k x (Nat.find h)).2
    some (R ∪ {v | v ∈ (loopErase p).vertices}, consume k p)
  else none

/-- A raw-cursor step and a cycle-popping step started with matching nonroot
cursors attach the same branch and leave matching cursors away from the new roots. -/
theorem rawStackStep_of_stackStep (head : V → D → V) (σ : V × ℕ → D)
    (R : Set V) (k l : Cursor V) (x : V) (S : Set V) (j : Cursor V)
    (hcursor : ∀ v, v ∉ R → k v = l v)
    (hstep : stackStep head (fun v i => σ (v, i)) R k x = some (S, j)) :
    ∃ m, rawStackStep head σ R l x = some (S, m) ∧
      ∀ v, v ∉ S → j v = m v := by
  letI : Quiver V := instructionQuiver head
  have hk : ∃ n, (instructionTrace head (fun v i => σ (v, i)) k x n).1 ∈ R := by
    by_contra hn
    simp only [stackStep, dif_neg hn] at hstep
    cases hstep
  let n := Nat.find hk
  have hfirst : ∀ i < n, (instructionTrace head (fun v j => σ (v, j)) k x i).1 ∉ R :=
    fun i hi => Nat.find_min hk hi
  have heq : instructionTrace head (fun v i => σ (v, i)) k x n =
      instructionTrace head (fun v i => σ (v, i)) l x n :=
    instructionTrace_eq_until_roots head R x k l σ n hcursor hfirst
  have hl : ∃ n, (instructionTrace head (fun v i => σ (v, i)) l x n).1 ∈ R :=
    ⟨n, (congrArg Sigma.fst heq) ▸ Nat.find_spec hk⟩
  have hln : Nat.find hl = n := by
    apply Nat.le_antisymm (Nat.find_min' hl (congrArg Sigma.fst heq ▸ Nat.find_spec hk))
    apply Nat.le_of_not_gt
    intro hlt
    have htrace := instructionTrace_eq_until_roots head R x k l σ (Nat.find hl)
      hcursor (fun i hi => hfirst i (lt_trans hi hlt))
    exact hfirst _ hlt ((congrArg Sigma.fst htrace).symm ▸ Nat.find_spec hl)
  let p := (instructionTrace head (fun v i => σ (v, i)) k x n).2
  let T := R ∪ {v | v ∈ (loopErase p).vertices}
  have hs : S = T ∧ j = erasedCursor k p := by
    simpa only [stackStep, dif_pos hk, Option.some.injEq, Prod.mk.injEq, n, p, T] using hstep.symm
  obtain ⟨rfl, rfl⟩ := hs
  refine ⟨consume l p, ?_, ?_⟩
  · simp only [rawStackStep, dif_pos hl]
    rw [hln, ← heq]
  · intro v hv
    have hvR : v ∉ R := fun h => hv (Or.inl h)
    have hvp : v ∉ (loopErase p).vertices := fun h => hv (Or.inr h)
    rw [erasedCursor_eq_consume_of_not_mem k p v hvp, consume_apply, consume_apply,
      hcursor v hvR]

/-- Explore a finite list while retaining the complete raw consumption cursor. -/
def rawStackExplore (head : V → D → V) (σ : V × ℕ → D) :
    Set V → Cursor V → List V → Option (Set V × Cursor V)
  | R, k, [] => some (R, k)
  | R, k, x :: xs => (rawStackStep head σ R k x).bind fun out =>
      rawStackExplore head σ out.1 out.2 xs

/-- The raw-consumption and cycle-popping explorations attach exactly the same
vertices for every successful finite ordered exploration. -/
theorem rawStackExplore_of_stackExplore (head : V → D → V) (σ : V × ℕ → D)
    (R : Set V) (k l : Cursor V) (L : List V) (S : Set V) (j : Cursor V)
    (hcursor : ∀ v, v ∉ R → k v = l v)
    (hstep : stackExplore head (fun v i => σ (v, i)) R k L = some (S, j)) :
    ∃ m, rawStackExplore head σ R l L = some (S, m) ∧
      ∀ v, v ∉ S → j v = m v := by
  induction L generalizing R k l with
  | nil =>
    simp only [stackExplore, Option.some.injEq, Prod.mk.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨l, rfl, hcursor⟩
  | cons x xs ih =>
    cases hs : stackStep head (fun v i => σ (v, i)) R k x with
    | none =>
      simp only [stackExplore, hs, Option.bind_none] at hstep
      cases hstep
    | some out =>
      obtain ⟨T, q⟩ := out
      have htail : stackExplore head (fun v i => σ (v, i)) T q xs = some (S, j) := by
        simpa only [stackExplore, hs, Option.bind_some] using hstep
      obtain ⟨r, hr, hqr⟩ := rawStackStep_of_stackStep head σ R k l x T q hcursor hs
      obtain ⟨m, hm, hfinal⟩ := ih T q r hqr htail
      refine ⟨m, ?_, hfinal⟩
      simpa only [rawStackExplore, hr, Option.bind_some] using hm

end
end FiniteAvalanches.Wilson.CyclePopping
