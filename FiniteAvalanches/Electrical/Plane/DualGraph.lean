import FiniteAvalanches.Electrical.Plane.ArcCycles
import FiniteAvalanches.Electrical.Dirichlet

/-! The copied dual graph of the actual augmented face quotient.
Its simple support is used only for reachability; all incidence algebra retains copies. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- One dual copy for every original edge, and one for the closing arc. -/
abbrev ArcEdge (E : Type*) := E ⊕ Unit

def arcForward {E : Type*} : ArcEdge E → ArcDart E
  | .inl e => .inl (e,false)
  | .inr _ => .inr false

/-- Both orientations of each copy, including the closing arc. -/
def arcDartEquiv (E : Type*) : Dart (ArcEdge E) ≃ ArcDart E where
  toFun d := match d with
    | (.inl e,c) => .inl (e,c)
    | (.inr _,c) => .inr c
  invFun d := match d with
    | .inl (e,c) => (.inl e,c)
    | .inr c => (.inr (),c)
  left_inv d := by rcases d with ⟨e,c⟩; cases e <;> rfl
  right_inv d := by cases d <;> rfl

@[simp] theorem arcDartEquiv_false {E : Type*} (e : ArcEdge E) :
    arcDartEquiv E (e,false) = arcForward e := by cases e <;> rfl

@[simp] theorem arcDartEquiv_true {E : Type*} (e : ArcEdge E) :
    arcDartEquiv E (e,true) = arcReverse E (arcForward e) := by cases e <;> rfl

/-- Primal copy endpoints, with the closing arc oriented alpha to beta. -/
def arcA {V E : Type*} (a : E → V) (alpha : V) : ArcEdge E → V
  | .inl e => a e
  | .inr _ => alpha

def arcB {V E : Type*} (b : E → V) (beta : V) : ArcEdge E → V
  | .inl e => b e
  | .inr _ => beta

@[simp] theorem arcTail_equiv {V E : Type*} (a b : E → V) (alpha beta : V)
    (d : Dart (ArcEdge E)) :
    arcTail a b alpha beta (arcDartEquiv E d) = tail (arcA a alpha) (arcB b beta) d := by
  rcases d with ⟨e,c⟩
  cases e <;> cases c <;> rfl

/-- Dual orientation is RIGHT to LEFT across the chosen forward primal dart. -/
noncomputable def dualA {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (da db : Dart E) (e : ArcEdge E) : ArcFace R da db :=
  arcRightFace R da db (arcForward e)

noncomputable def dualB {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (da db : Dart E) (e : ArcEdge E) : ArcFace R da db :=
  arcLeftFace R da db (arcForward e)

/-- The actual face endpoints of every oriented copied primal incidence. -/
theorem dual_faces_equiv {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (da db : Dart E) (d : Dart (ArcEdge E)) :
    arcRightFace R da db (arcDartEquiv E d) = tail (dualA R da db) (dualB R da db) d ∧
    arcLeftFace R da db (arcDartEquiv E d) = head (dualA R da db) (dualB R da db) d := by
  rcases d with ⟨e,c⟩
  cases e <;> cases c <;> exact ⟨rfl,rfl⟩

/-- Loops in the dual (including primal bridges) are reflexive reachability steps. -/
theorem dual_faces_reachable {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (da db : Dart E) (d : ArcDart E) :
    (supportGraph (dualA R da db) (dualB R da db)).Reachable
      (arcLeftFace R da db d) (arcRightFace R da db d) := by
  let e := (arcDartEquiv E).symm d
  have he := dual_faces_equiv R da db e
  rw [(arcDartEquiv E).apply_symm_apply] at he
  let G := supportGraph (dualA R da db) (dualB R da db)
  have step (k : ArcEdge E) : G.Reachable (dualB R da db k) (dualA R da db k) := by
    by_cases h : dualB R da db k = dualA R da db k
    · rw [h]
    · exact (show G.Adj _ _ from ⟨h,k,Or.inr ⟨rfl,rfl⟩⟩).reachable
  rw [he.1,he.2]
  rcases e with ⟨e,c⟩
  cases c
  · exact step e
  · exact (step e).symm

/-- Primal connectedness implies dual connectedness for the actual rotation-face quotient.
No Euler or genus-zero claim is used. -/
theorem dual_preconnected {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hconn : (supportGraph a b).Preconnected) :
    (supportGraph (dualA R da db) (dualB R da db)).Preconnected := by
  let G := supportGraph (dualA R da db) (dualB R da db)
  have hrev (d : ArcDart E) : G.Reachable (arcLeftFace R da db d)
      (arcLeftFace R da db (arcReverse E d)) := dual_faces_reachable R da db d
  have hnext (d : ArcDart E) : G.Reachable (arcLeftFace R da db d)
      (arcLeftFace R da db (insertArcRotation R da db d)) := by
    rw [arcLeftFace_next]
    exact hrev d
  have hcycle (d d' : ArcDart E) (h : (insertArcRotation R da db).SameCycle d d') :
      G.Reachable (arcLeftFace R da db d) (arcLeftFace R da db d') := by
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hp : ∀ n : ℕ, G.Reachable (arcLeftFace R da db d)
        (arcLeftFace R da db (((insertArcRotation R da db)^n) d)) := by
      intro n
      induction n with
      | zero => exact .rfl
      | succ n ih =>
        rw [pow_succ',Equiv.Perm.mul_apply]
        exact ih.trans (hnext _)
    simpa only [hn] using hp n
  have hvertex (d d' : ArcDart E) (h : arcTail a b alpha beta d = arcTail a b alpha beta d') :
      G.Reachable (arcLeftFace R da db d) (arcLeftFace R da db d') :=
    hcycle d d' ((insertArcRotation_sameCycle_iff R alpha beta hne da db ha hb d d').mpr h)
  let P := fun x : V => ∀ d : ArcDart E, arcTail a b alpha beta d = x →
    G.Reachable (arcLeftFace R da db (.inr false)) (arcLeftFace R da db d)
  have hPa : P alpha := fun d hd => hvertex (.inr false) d hd.symm
  have hstep : ∀ {x y}, (supportGraph a b).Adj x y → P x → P y := by
    intro x y hadj hx
    obtain ⟨_,e,he⟩ := hadj
    have move (d : Dart E) (ht : tail a b d = x) (hh : head a b d = y) : P y := by
      intro d' hd'
      exact ((hx (.inl d) ht).trans (hrev (.inl d))).trans
        (hvertex (arcReverse E (.inl d)) d' (hh.trans hd'.symm))
    rcases he with he | he
    · exact move (e,false) he.1 he.2
    · exact move (e,true) he.1 he.2
  have hwalk {x y} (w : (supportGraph a b).Walk x y) : P x → P y := by
    induction w with
    | nil => exact id
    | cons h w ih => exact fun hx => ih (hstep h hx)
  have hP (x : V) : P x := by
    obtain ⟨w⟩ := hconn alpha x
    exact hwalk w hPa
  intro f g
  induction f using Quotient.inductionOn with
  | _ d =>
    induction g using Quotient.inductionOn with
    | _ d' =>
      exact (hP _ d rfl).symm.trans (hP _ d' rfl)

end FiniteAvalanches.Electrical.Plane
