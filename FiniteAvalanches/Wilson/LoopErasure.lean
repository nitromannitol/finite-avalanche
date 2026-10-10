import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Tactic

/-! Chronological loop erasure on endpoint-indexed walks. Quiver arrows are
retained, so a surviving edge keeps its original copy, even for parallel edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson

open Quiver

variable {V : Type*} [Quiver V] [DecidableEq V]

/-- Truncate at the last occurrence of a vertex. On a simple retained path
this is its unique occurrence. The output retains the original arrows. -/
def prefixTo {a : V} : {b : V} → (p : Path a b) → (v : V) → v ∈ p.vertices → Path a v
  | _, .nil, v, hv => by
      have h : v = a := by simpa using hv
      subst v
      exact .nil
  | b, .cons p e, v, hv =>
      if h : b = v then h ▸ p.cons e
      else prefixTo p v ((Quiver.Path.mem_vertices_cons p e).mp hv |>.resolve_right (Ne.symm h))

/-- Online chronological loop erasure: visit vertices in their original order,
retain new arrows, and erase the retained suffix whenever a vertex is revisited. -/
def loopErase {a : V} : {b : V} → Path a b → Path a b
  | _, .nil => .nil
  | b, .cons p e =>
      let q := loopErase p
      if h : b ∈ q.vertices then prefixTo q b h else q.cons e

theorem prefixTo_vertices_sublist {a b : V} (p : Path a b) (v : V) (hv : v ∈ p.vertices) :
    (prefixTo p v hv).vertices.Sublist p.vertices := by
  induction p with
  | nil =>
      have h : v = a := by simpa using hv
      subst v
      simp [prefixTo]
  | @cons b c p e ih =>
      by_cases h : c = v
      · subst v
        simp [prefixTo]
      · simp only [prefixTo, dif_neg h]
        exact (ih _).trans (by simp [Quiver.Path.vertices_cons])

theorem prefixTo_vertices_nodup {a b : V} (p : Path a b) (v : V) (hv : v ∈ p.vertices)
    (hp : p.vertices.Nodup) : (prefixTo p v hv).vertices.Nodup :=
  hp.sublist (prefixTo_vertices_sublist p v hv)

theorem loopErase_vertices_sublist {a b : V} (p : Path a b) :
    (loopErase p).vertices.Sublist p.vertices := by
  induction p with
  | nil => simp [loopErase]
  | @cons b c p e ih =>
      by_cases h : c ∈ (loopErase p).vertices
      · simp only [loopErase, dif_pos h]
        exact (prefixTo_vertices_sublist _ _ h).trans
          (ih.trans (by simp [Quiver.Path.vertices_cons]))
      · simp only [loopErase, dif_neg h, Quiver.Path.vertices_cons, List.concat_eq_append]
        exact ih.append (List.Sublist.refl [c])

theorem loopErase_vertices_nodup {a b : V} (p : Path a b) : (loopErase p).vertices.Nodup := by
  induction p with
  | nil => simp [loopErase]
  | @cons b c p e ih =>
      by_cases h : c ∈ (loopErase p).vertices
      · simp only [loopErase, dif_pos h]
        exact prefixTo_vertices_nodup _ _ h ih
      · simp only [loopErase, dif_neg h, Quiver.Path.vertices_cons]
        exact ih.concat h

theorem loopErase_eq_self {a b : V} (p : Path a b) (hp : p.vertices.Nodup) : loopErase p = p := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      have hpair : c ∉ p.vertices ∧ p.vertices.Nodup :=
        (List.nodup_concat p.vertices c).mp hp
      rw [loopErase, ih hpair.2, dif_neg hpair.1]


@[simp] theorem loopErase_head {a b : V} (p : Path a b) :
    (loopErase p).vertices.head? = some a := Quiver.Path.vertices_head? _

@[simp] theorem loopErase_terminal {a b : V} (p : Path a b) :
    (loopErase p).vertices.getLast (Quiver.Path.vertices_ne_nil _) = b :=
  Quiver.Path.vertices_getLast _ _

theorem loopErase_length_le {a b : V} (p : Path a b) : (loopErase p).length ≤ p.length := by
  have h := (loopErase_vertices_sublist p).length_le
  simp only [Quiver.Path.vertices_length] at h
  omega

/-- The quiver of individual unoriented edge copies with their actual endpoints. -/
abbrev copiedQuiver {E : Type*} (ends : E → V × V) : Quiver V where
  Hom x y := {e : E // (ends e = (x, y)) ∨ (ends e = (y, x))}

end FiniteAvalanches.Wilson
