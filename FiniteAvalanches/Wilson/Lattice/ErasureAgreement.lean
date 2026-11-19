import FiniteAvalanches.Wilson.Lattice.StackWalkLaw
import FiniteAvalanches.Wilson.Lattice.Sampler
import FiniteAvalanches.Wilson.LoopErasureComposition
import Mathlib.Data.List.TakeWhile

/-! The list and quiver versions of chronological lattice loop erasure agree. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson
open FiniteAvalanches.Wilson.CyclePopping FiniteAvalanches.Sandpile
open scoped Classical

noncomputable section

private theorem takeWhile_ne_append_of_mem (l m : List (Site 2)) (v : Site 2) (hv : v ∈ l) :
    (l ++ m).takeWhile (fun u => decide (u ≠ v)) = l.takeWhile (fun u => decide (u ≠ v)) := by
  induction l with
  | nil => simp at hv
  | cons x xs ih =>
    by_cases hx : x = v
    · subst x
      simp
    · have hv' : v ∈ xs := (List.mem_cons.mp hv).resolve_left (Ne.symm hx)
      simp only [List.cons_append, List.takeWhile_cons, decide_eq_true_eq, if_pos hx]
      exact congrArg (List.cons x) (ih hv')

private theorem takeWhile_ne_append_singleton_of_not_mem (l : List (Site 2)) (v : Site 2)
    (hv : v ∉ l) : (l ++ [v]).takeWhile (fun u => decide (u ≠ v)) = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≠ v := fun h => hv (h ▸ List.mem_cons_self)
    have hv' : v ∉ xs := fun h => hv (List.mem_cons_of_mem _ h)
    simp only [List.cons_append, List.takeWhile_cons, decide_eq_true_eq, if_pos hx]
    exact congrArg (List.cons x) (ih hv')

/-- On a simple quiver path, truncation agrees with the corresponding list prefix. -/
theorem prefixTo_vertices_eq_takeWhile [Quiver (Site 2)] {a b : Site 2}
    (p : Quiver.Path a b) (hp : p.vertices.Nodup) (v : Site 2) (hv : v ∈ p.vertices) :
    (prefixTo p v hv).vertices = p.vertices.takeWhile (fun u => decide (u ≠ v)) ++ [v] := by
  induction p with
  | nil =>
    have he : v = a := by simpa using hv
    subst v
    simp [prefixTo, Quiver.Path.vertices]
  | @cons b c p e ih =>
    have hn := (List.nodup_concat p.vertices c).mp hp
    by_cases hc : c = v
    · subst c
      rw [prefixTo_self]
      rw [Quiver.Path.vertices_cons, List.concat_eq_append,
        takeWhile_ne_append_singleton_of_not_mem p.vertices v hn.1]
    · have hv' : v ∈ p.vertices :=
        ((Quiver.Path.mem_vertices_cons p e).mp hv).resolve_right (Ne.symm hc)
      rw [prefixTo_cons_of_ne p e hv hc hv', ih hn.2 hv']
      rw [Quiver.Path.vertices_cons, List.concat_eq_append,
        takeWhile_ne_append_of_mem p.vertices [c] v hv']

/-- Appending an arrow and erasing cycles matches one list-erasure step. -/
theorem loopErase_cons_vertices [Quiver (Site 2)] {a b c : Site 2}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    (loopErase (p.cons e)).vertices = eraseStep (loopErase p).vertices c := by
  rw [loopErase_cons_eq]
  by_cases hc : c ∈ (loopErase p).vertices
  · rw [dif_pos hc, prefixTo_vertices_eq_takeWhile (loopErase p)
      (loopErase_vertices_nodup p) c hc]
    rfl
  · rw [dif_neg hc, Quiver.Path.vertices_cons, List.concat_eq_append]
    unfold eraseStep
    have ht : (loopErase p).vertices.takeWhile (fun u => decide (u ≠ c)) =
        (loopErase p).vertices := by
      apply List.takeWhile_eq_self_iff.mpr
      intro v hv
      simp only [decide_eq_true_eq]
      exact fun h => hc (h ▸ hv)
    rw [ht]

private theorem walkErase_succ_local (x : Site 2) (w : WalkDriver) (T : ℕ) :
    walkErase x w (T + 1) = eraseStep (walkErase x w T) (position x w (T + 1)) := by
  simp only [walkErase, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The lattice stack trace and the sampler's list algorithm have the same
chronological loop-erased vertices. -/
theorem stackTrace_loopErase_vertices (x : Site 2) (k : Cursor (Site 2))
    (σ : Site 2 × ℕ → FiniteWired.Direction) :
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    ∀ n, (loopErase (instructionTrace latticeDirectionHead (fun v i => σ (v, i)) k x n).2).vertices =
      walkErase x (readingLetter latticeDirectionHead x k σ) n := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  intro n
  induction n with
  | zero => simp [instructionTrace, loopErase, walkErase, eraseStep]
  | succ n ih =>
    change (loopErase ((instructionTrace latticeDirectionHead (fun v i => σ (v, i)) k x n).2.cons _)).vertices = _
    rw [loopErase_cons_vertices, ih, walkErase_succ_local]
    congr 1
    exact lattice_instructionTrace_position x k σ (n + 1)

end
end FiniteAvalanches.Wilson.Lattice
