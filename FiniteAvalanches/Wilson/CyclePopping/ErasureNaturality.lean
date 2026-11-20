import FiniteAvalanches.Wilson.LoopErasureComposition
import Mathlib.Data.List.TakeWhile

/-! Loop-erased vertex lists commute with injective vertex maps. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Append a vertex to a chronologically loop-erased list. -/
def eraseVertex (l : List V) (v : V) : List V :=
  l.takeWhile (fun u => decide (u ≠ v)) ++ [v]

private theorem takeWhile_ne_append_of_mem (l m : List V) (v : V) (hv : v ∈ l) :
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

private theorem takeWhile_ne_append_singleton_of_not_mem (l : List V) (v : V)
    (hv : v ∉ l) : (l ++ [v]).takeWhile (fun u => decide (u ≠ v)) = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≠ v := fun h => hv (h ▸ List.mem_cons_self)
    have hv' : v ∉ xs := fun h => hv (List.mem_cons_of_mem _ h)
    simp only [List.cons_append, List.takeWhile_cons, decide_eq_true_eq, if_pos hx]
    exact congrArg (List.cons x) (ih hv')

/-- The vertices of a truncated simple path are the corresponding list prefix. -/
theorem prefixTo_vertices_eq_erasePrefix [Quiver V] {a b : V}
    (p : Path a b) (hp : p.vertices.Nodup) (v : V) (hv : v ∈ p.vertices) :
    (prefixTo p v hv).vertices = eraseVertex p.vertices v := by
  induction p with
  | nil =>
    have he : v = a := by simpa using hv
    subst v
    simp [prefixTo, Path.vertices, eraseVertex]
  | @cons b c p e ih =>
    have hn := (List.nodup_concat p.vertices c).mp hp
    by_cases hc : c = v
    · subst c
      rw [prefixTo_self]
      rw [Path.vertices_cons, List.concat_eq_append]
      simp only [eraseVertex, takeWhile_ne_append_singleton_of_not_mem p.vertices v hn.1]
    · have hv' : v ∈ p.vertices :=
        ((Path.mem_vertices_cons p e).mp hv).resolve_right (Ne.symm hc)
      rw [prefixTo_cons_of_ne p e hv hc hv', ih hn.2 hv']
      simp only [eraseVertex, Path.vertices_cons, List.concat_eq_append,
        takeWhile_ne_append_of_mem p.vertices [c] v hv']

/-- The vertex list of loop erasure is obtained by online list erasure. -/
theorem loopErase_vertices_fold [Quiver V] {a b : V} (p : Path a b) :
    (loopErase p).vertices = p.vertices.foldl eraseVertex [] := by
  induction p with
  | nil => simp [loopErase, Path.vertices, eraseVertex]
  | @cons b c p e ih =>
    rw [Path.vertices_cons, List.concat_eq_append, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ← ih, loopErase_cons_eq]
    by_cases hc : c ∈ (loopErase p).vertices
    · rw [dif_pos hc, prefixTo_vertices_eq_erasePrefix _ (loopErase_vertices_nodup p) c hc]
    · rw [dif_neg hc, Path.vertices_cons, List.concat_eq_append]
      unfold eraseVertex
      have ht : (loopErase p).vertices.takeWhile (fun u => decide (u ≠ c)) =
          (loopErase p).vertices := by
        apply List.takeWhile_eq_self_iff.mpr
        intro v hv
        simp only [decide_eq_true_eq]
        exact fun h => hc (h ▸ hv)
      rw [ht]

/-- Online loop erasure commutes with an injective relabeling of vertices. -/
theorem map_eraseVertex (f : V → W) (hf : Function.Injective f) (l : List V) (v : V) :
    (eraseVertex l v).map f = eraseVertex (l.map f) (f v) := by
  induction l with
  | nil => simp [eraseVertex]
  | cons x xs ih =>
    by_cases hx : x = v
    · subst x
      simp [eraseVertex]
    · have hfx : f x ≠ f v := fun h => hx (hf h)
      simp only [eraseVertex, List.takeWhile_cons, decide_eq_true_eq, if_pos hx,
        List.map_cons, if_pos hfx, List.cons_append, List.map_cons] at ih ⊢
      exact congrArg (List.cons (f x)) ih

/-- The online erasure of any finite vertex word is equivariant under an
injective relabeling. -/
theorem map_fold_eraseVertex (f : V → W) (hf : Function.Injective f)
    (l acc : List V) :
    (l.foldl eraseVertex acc).map f = (l.map f).foldl eraseVertex (acc.map f) := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, ← map_eraseVertex f hf]
    exact ih (eraseVertex acc x)

/-- Paths with the same vertices after an injective relabeling have the same
loop-erased vertices after that relabeling. -/
theorem loopErase_vertices_map_eq [Quiver V] [Quiver W] (f : V → W)
    (hf : Function.Injective f) {a b : V} {c d : W} (p : Path a b) (q : Path c d)
    (h : p.vertices.map f = q.vertices) :
    (loopErase p).vertices.map f = (loopErase q).vertices := by
  rw [loopErase_vertices_fold, loopErase_vertices_fold, map_fold_eraseVertex f hf,
    List.map_nil, h]

end FiniteAvalanches.Wilson.CyclePopping
