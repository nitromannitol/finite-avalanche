import FiniteAvalanches.Wilson.CyclePopping.Basic

/-! Separating popped stack entries from the terminal arrows in cycle popping. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open scoped Classical

noncomputable section

variable {V : Type*} {A : V → Type*}

/-- Replace each stack entry at its specified cursor, leaving all other entries intact. -/
def replaceTop (σ : Stacks A) (k : Cursor V) (a : (v : V) → A v) : Stacks A :=
  fun v i => if i = k v then a v else σ v i

/-- A replacement at the cursor does not change the popped prefix. -/
theorem replaceTop_below (σ : Stacks A) (k : Cursor V) (a : (v : V) → A v)
    (v : V) (i : ℕ) (hi : i < k v) : replaceTop σ k a v i = σ v i := by
  simp only [replaceTop, if_neg (Nat.ne_of_lt hi)]

/-- The new top entries are exactly the specified instructions. -/
theorem top_replaceTop (σ : Stacks A) (k : Cursor V) (a : (v : V) → A v) :
    top (replaceTop σ k a) k = a := by
  funext v
  simp only [top, replaceTop, ↓reduceIte]

variable [DecidableEq V]

/-- Replacing the top cells preserves every legal run ending at the given cursor. -/
theorem pop_run_replaceTop_iff (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k l : Cursor V) (a : (v : V) → A v) :
    Relation.ReflTransGen (pop_step R head (replaceTop σ l a)) k l ↔
      Relation.ReflTransGen (pop_step R head σ) k l := by
  apply pop_run_iff_of_agree_below R head
  intro v i hi
  exact replaceTop_below σ l a v i hi

/-- A terminal run ending at a given cursor consists independently of a legal popped
prefix and a cycle-free selection of the top instructions. -/
theorem terminal_run_replaceTop_iff (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k l : Cursor V) (a : (v : V) → A v) :
    (Relation.ReflTransGen (pop_step R head (replaceTop σ l a)) k l ∧
      terminal R head (replaceTop σ l a) l) ↔
    (Relation.ReflTransGen (pop_step R head σ) k l ∧
      ∀ c : Finset V, ¬ IsCycle R (fun v => head v (a v)) c) := by
  rw [pop_run_replaceTop_iff]
  have hn : next head (replaceTop σ l a) l = fun v => head v (a v) := by
    funext v
    simp only [next, top_replaceTop]
  simp only [terminal, hn]

end
end FiniteAvalanches.Wilson.CyclePopping
