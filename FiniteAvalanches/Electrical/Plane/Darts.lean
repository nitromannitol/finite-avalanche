import FiniteAvalanches.Electrical.Energy
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Logic.Equiv.Sum

/-! Individually indexed darts and actual rotation-face orbits.
A rotation system is not, by itself, a genus-zero embedding. -/

namespace FiniteAvalanches.Electrical.Plane

open scoped BigOperators Classical

/-- Each original edge copy has two orientations. False runs from a to b. -/
abbrev Dart (E : Type*) := E × Bool

def tail {V E : Type*} (a b : E → V) (d : Dart E) : V :=
  if d.2 then b d.1 else a d.1

/-- Reversal retains the original edge index, including parallel copies. -/
def reverse (E : Type*) : Equiv.Perm (Dart E) where
  toFun d := (d.1,!d.2)
  invFun d := (d.1,!d.2)
  left_inv d := by rcases d with ⟨e,h⟩; cases h <;> rfl
  right_inv d := by rcases d with ⟨e,h⟩; cases h <;> rfl

def head {V E : Type*} (a b : E → V) (d : Dart E) : V := tail a b (reverse E d)

@[simp] theorem reverse_reverse {E : Type*} (d : Dart E) : reverse E (reverse E d) = d := by
  rcases d with ⟨e,h⟩; cases h <;> rfl

@[simp] theorem tail_reverse {V E : Type*} (a b : E → V) (d : Dart E) :
    tail a b (reverse E d) = head a b d := rfl

@[simp] theorem head_reverse {V E : Type*} (a b : E → V) (d : Dart E) :
    head a b (reverse E d) = tail a b d := by simp [head]

/-- Physical signed current: positive from higher to lower voltage. -/
def current {V E : Type*} (a b : E → V) (phi : V → ℝ) (d : Dart E) : ℝ :=
  phi (tail a b d)-phi (head a b d)

@[simp] theorem current_reverse {V E : Type*} (a b : E → V) (phi : V → ℝ) (d : Dart E) :
    current a b phi (reverse E d) = -current a b phi d := by simp [current]

/-- Clockwise cyclic order at each vertex, expressed on the actual incidence fiber. -/
structure EdgeRotation {V E : Type*} (a b : E → V) where
  next : Equiv.Perm (Dart E)
  cycles : ∀ d d', next.SameCycle d d' ↔ tail a b d = tail a b d'

theorem EdgeRotation.tail_next {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (d : Dart E) : tail a b (R.next d) = tail a b d := by
  apply ((R.cycles d (R.next d)).mp _).symm
  exact ⟨1,by simp⟩

/-- Walk along the left face: reverse at the head, then take its clockwise successor. -/
def EdgeRotation.faceNext {V E : Type*} {a b : E → V} (R : EdgeRotation a b) :
    Equiv.Perm (Dart E) := (reverse E).trans R.next

/-- Faces are actual orbits of the face-walk permutation. -/
abbrev EdgeRotation.Face {V E : Type*} {a b : E → V} (R : EdgeRotation a b) :=
  Quotient (Equiv.Perm.SameCycle.setoid R.faceNext)

noncomputable instance {V E : Type*} [Fintype E] {a b : E → V} (R : EdgeRotation a b) :
    Fintype R.Face := Fintype.ofFinite _

def EdgeRotation.leftFace {V E : Type*} {a b : E → V} (R : EdgeRotation a b) (d : Dart E) :
    R.Face := Quotient.mk _ d

def EdgeRotation.rightFace {V E : Type*} {a b : E → V} (R : EdgeRotation a b) (d : Dart E) :
    R.Face := R.leftFace (reverse E d)

theorem EdgeRotation.leftFace_faceNext {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (d : Dart E) : R.leftFace (R.faceNext d) = R.leftFace d := by
  apply Quotient.sound
  exact (show R.faceNext.SameCycle d (R.faceNext d) from ⟨1,by simp⟩).symm

theorem EdgeRotation.leftFace_next {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (d : Dart E) : R.leftFace (R.next d) = R.rightFace d := by
  have h := R.leftFace_faceNext (reverse E d)
  simpa only [EdgeRotation.faceNext, Equiv.trans_apply, reverse_reverse,
    EdgeRotation.rightFace] using h

/-- Outgoing incidence sum, with every original copy retained. -/
noncomputable def divergence {V E : Type*} [Fintype E] (a b : E → V)
    (phi : V → ℝ) (x : V) : ℝ :=
  ∑ d : Dart E, if tail a b d = x then current a b phi d else 0

theorem divergence_eq_laplacian {V E : Type*} [Fintype E]
    (a b : E → V) (phi : V → ℝ) (x : V) :
    divergence a b phi x = FiniteAvalanches.Electrical.laplacian a b phi x := by
  simp only [divergence, Fintype.sum_prod_type, Fintype.sum_bool, current, head,
    reverse, tail, Bool.false_eq_true, ↓reduceIte]
  unfold FiniteAvalanches.Electrical.laplacian
  apply Finset.sum_congr rfl
  intro e _
  split <;> split <;> simp_all

end FiniteAvalanches.Electrical.Plane
