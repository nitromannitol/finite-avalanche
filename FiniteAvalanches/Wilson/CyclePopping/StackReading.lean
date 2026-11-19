import FiniteAvalanches.Wilson.CyclePopping.Basic
import Mathlib.Order.Monotone.Basic

/-! Adaptive chronological reading of vertex instruction stacks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open scoped Classical

noncomputable section

variable {V D : Type*} [DecidableEq V]

/-- Position and per-vertex consumption cursors driven by a prescribed instruction word. -/
def wordState (head : V → D → V) (x : V) (k : Cursor V) (w : ℕ → D) : ℕ → V × Cursor V
  | 0 => (x, k)
  | n + 1 =>
    let s := wordState head x k w n
    (head s.1 (w n), pop s.2 {s.1})

/-- The stack coordinate read at a given time when following a prescribed word. -/
def wordAddress (head : V → D → V) (x : V) (k : Cursor V) (w : ℕ → D) (n : ℕ) : V × ℕ :=
  let s := wordState head x k w n
  (s.1, s.2 s.1)

/-- Stack cursors along a prescribed word are coordinatewise monotone. -/
theorem wordState_cursor_mono (head : V → D → V) (x : V) (k : Cursor V) (w : ℕ → D) :
    Monotone (fun n => (wordState head x k w n).2) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_pop _ _

/-- A chronological exploration never reads the same stack coordinate twice. -/
theorem wordAddress_injective (head : V → D → V) (x : V) (k : Cursor V) (w : ℕ → D) :
    Function.Injective (wordAddress head x k w) := by
  intro i j h
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hp : (wordState head x k w i).1 = (wordState head x k w j).1 := by simpa only [wordAddress] using congrArg Prod.fst h
    have hc : (wordState head x k w i).2 (wordState head x k w i).1 =
        (wordState head x k w j).2 (wordState head x k w j).1 := by simpa only [wordAddress] using congrArg Prod.snd h
    have hm := wordState_cursor_mono head x k w (Nat.succ_le_of_lt hij)
      (wordState head x k w i).1
    change pop (wordState head x k w i).2 {(wordState head x k w i).1}
      (wordState head x k w i).1 ≤
        (wordState head x k w j).2 (wordState head x k w i).1 at hm
    rw [pop_apply_of_mem _ _ (Finset.mem_singleton_self _)] at hm
    have hc' : (wordState head x k w j).2 (wordState head x k w i).1 =
        (wordState head x k w i).2 (wordState head x k w i).1 := by simpa only [← hp] using hc.symm
    rw [hc'] at hm
    exact Nat.not_succ_le_self _ hm
  · have hp : (wordState head x k w j).1 = (wordState head x k w i).1 := by simpa only [wordAddress] using (congrArg Prod.fst h).symm
    have hc : (wordState head x k w j).2 (wordState head x k w j).1 =
        (wordState head x k w i).2 (wordState head x k w i).1 := by simpa only [wordAddress] using (congrArg Prod.snd h).symm
    have hm := wordState_cursor_mono head x k w (Nat.succ_le_of_lt hji)
      (wordState head x k w j).1
    change pop (wordState head x k w j).2 {(wordState head x k w j).1}
      (wordState head x k w j).1 ≤
        (wordState head x k w i).2 (wordState head x k w j).1 at hm
    rw [pop_apply_of_mem _ _ (Finset.mem_singleton_self _)] at hm
    have hc' : (wordState head x k w i).2 (wordState head x k w j).1 =
        (wordState head x k w j).2 (wordState head x k w j).1 := by simpa only [← hp] using hc.symm
    rw [hc'] at hm
    exact Nat.not_succ_le_self _ hm

/-- Position and cursors when the next instruction is read from the current stack. -/
def readingState (head : V → D → V) (x : V) (k : Cursor V) (σ : V × ℕ → D) : ℕ → V × Cursor V
  | 0 => (x, k)
  | n + 1 =>
    let s := readingState head x k σ n
    (head s.1 (σ (s.1, s.2 s.1)), pop s.2 {s.1})

/-- The instruction read at time `n` in the adaptive stack walk. -/
def readingLetter (head : V → D → V) (x : V) (k : Cursor V) (σ : V × ℕ → D)
    (n : ℕ) : D :=
  let s := readingState head x k σ n
  σ (s.1, s.2 s.1)

/-- If a prescribed word matches its stack coordinates, the adaptive state follows that word. -/
theorem readingState_eq_wordState (head : V → D → V) (x : V) (k : Cursor V)
    (σ : V × ℕ → D) (w : ℕ → D) (n : ℕ)
    (h : ∀ i < n, σ (wordAddress head x k w i) = w i) :
    readingState head x k σ n = wordState head x k w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    change (head (readingState head x k σ n).1
        (σ ((readingState head x k σ n).1,
          (readingState head x k σ n).2 (readingState head x k σ n).1)),
        pop (readingState head x k σ n).2 {(readingState head x k σ n).1}) = _
    rw [he]
    change (head (wordState head x k w n).1 (σ (wordAddress head x k w n)),
      pop (wordState head x k w n).2 {(wordState head x k w n).1}) = _
    rw [hn]
    rfl

/-- A read prefix equals a prescribed word exactly when the corresponding
pairwise-distinct stack coordinates contain that word. -/
theorem reading_prefix_iff (head : V → D → V) (x : V) (k : Cursor V)
    (σ : V × ℕ → D) (w : ℕ → D) (n : ℕ) :
    (∀ i < n, readingLetter head x k σ i = w i) ↔
      ∀ i < n, σ (wordAddress head x k w i) = w i := by
  constructor
  · intro h i hi
    have hp : ∀ j < i, σ (wordAddress head x k w j) = w j := by
      intro j hj
      induction j using Nat.strong_induction_on with
      | h j ih =>
        have he := readingState_eq_wordState head x k σ w j
          (fun q hq => ih q hq (lt_trans hq hj))
        have hh := h j (lt_trans hj hi)
        simpa only [readingLetter, wordAddress, he] using hh
    have he := readingState_eq_wordState head x k σ w i hp
    have hh := h i hi
    simpa only [readingLetter, wordAddress, he] using hh
  · intro h i hi
    have he := readingState_eq_wordState head x k σ w i (fun j hj => h j (lt_trans hj hi))
    have hh := h i hi
    simpa only [readingLetter, wordAddress, he] using hh

end
end FiniteAvalanches.Wilson.CyclePopping
