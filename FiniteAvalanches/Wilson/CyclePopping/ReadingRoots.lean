import FiniteAvalanches.Wilson.CyclePopping.ReadingLocality
import FiniteAvalanches.Wilson.CyclePopping.Erasure

/-! Stack readings stopped at roots are unaffected by cursor changes on roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V D : Type*} [DecidableEq V]

/-- The cursor after deleting loops agrees with the fully consumed cursor away
from the retained loop-erased path. -/
theorem erasedCursor_eq_consume_of_not_mem [Quiver V] (k : Cursor V) {a b : V}
    (p : Path a b) (v : V) (hv : v ∉ (loopErase p).vertices) :
    erasedCursor k p v = consume k p v := by
  have hn : v ∉ departures (loopErase p) := by
    intro hm
    exact hv (List.dropLast_sublist _ |>.subset hm)
  simp only [erasedCursor, List.count_eq_zero_of_not_mem hn, Nat.sub_zero]

/-- If two initial cursors agree away from the roots, their stack walks agree
until the first root, including the directions read before that time. -/
theorem readingState_eq_until_roots (head : V → D → V) (R : Set V) (x : V)
    (k l : Cursor V) (σ : V × ℕ → D) (n : ℕ)
    (hcursor : ∀ v, v ∉ R → k v = l v)
    (havoid : ∀ i < n, (readingState head x k σ i).1 ∉ R) :
    (readingState head x k σ n).1 = (readingState head x l σ n).1 ∧
      (∀ v, v ∉ R → (readingState head x k σ n).2 v =
        (readingState head x l σ n).2 v) ∧
      ∀ i < n, readingLetter head x k σ i = readingLetter head x l σ i := by
  induction n with
  | zero => exact ⟨rfl, hcursor, by simp⟩
  | succ n ih =>
    obtain ⟨hp, hc, hl⟩ := ih (fun i hi => havoid i (Nat.lt_succ_of_lt hi))
    have hn := havoid n (Nat.lt_succ_self n)
    have hletter : readingLetter head x k σ n = readingLetter head x l σ n := by
      simp only [readingLetter, ← hp, hc _ hn]
    refine ⟨?_, ?_, ?_⟩
    · change head (readingState head x k σ n).1 (readingLetter head x k σ n) =
        head (readingState head x l σ n).1 (readingLetter head x l σ n)
      rw [hp, hletter]
    · intro v hv
      change pop (readingState head x k σ n).2 {(readingState head x k σ n).1} v =
        pop (readingState head x l σ n).2 {(readingState head x l σ n).1} v
      rw [← hp]
      by_cases he : v = (readingState head x k σ n).1
      · subst v
        rw [pop_apply_of_mem _ _ (Finset.mem_singleton_self _),
          pop_apply_of_mem _ _ (Finset.mem_singleton_self _), hc _ hv]
      · rw [pop_apply_of_not_mem _ _ (fun h => he (Finset.mem_singleton.mp h)),
          pop_apply_of_not_mem _ _ (fun h => he (Finset.mem_singleton.mp h)), hc _ hv]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hl i hi
      · exact hletter

/-- Once the retained path has become part of the root set, continuing from
its erased cursor gives the same walk up to the roots as the fully consumed cursor. -/
theorem readingState_eq_until_roots_of_erasure [Quiver V] (head : V → D → V)
    (R : Set V) (x : V) (k : Cursor V) {a b : V} (p : Path a b)
    (hroots : ∀ v ∈ (loopErase p).vertices, v ∈ R) (σ : V × ℕ → D) (n : ℕ)
    (havoid : ∀ i < n, (readingState head x (consume k p) σ i).1 ∉ R) :
    (readingState head x (consume k p) σ n).1 =
        (readingState head x (erasedCursor k p) σ n).1 ∧
      (∀ v, v ∉ R → (readingState head x (consume k p) σ n).2 v =
        (readingState head x (erasedCursor k p) σ n).2 v) ∧
      ∀ i < n, readingLetter head x (consume k p) σ i =
        readingLetter head x (erasedCursor k p) σ i := by
  apply readingState_eq_until_roots head R x (consume k p) (erasedCursor k p) σ n
  · intro v hv
    exact (erasedCursor_eq_consume_of_not_mem k p v (fun hm => hv (hroots v hm))).symm
  · exact havoid

end
end FiniteAvalanches.Wilson.CyclePopping
