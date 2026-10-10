import FiniteAvalanches.Electrical.Plane.Darts
import FiniteAvalanches.Electrical.Response

/-! The auxiliary outer-face arc as a geometric dart pair, not an energy edge. -/
namespace FiniteAvalanches.Electrical.Plane

open scoped BigOperators Classical

/-- Original darts are unchanged; the two new darts belong only to the auxiliary arc. -/
abbrev ArcDart (E : Type*) := Dart E ⊕ Bool

def arcTail {V E : Type*} (a b : E → V) (alpha beta : V) : ArcDart E → V
  | .inl d => tail a b d
  | .inr false => alpha
  | .inr true => beta

def arcReverse (E : Type*) : Equiv.Perm (ArcDart E) :=
  Equiv.sumCongr (reverse E) (Equiv.swap false true)

/-- Insert alpha's and beta's arc darts after the indicated outgoing incidences. -/
noncomputable def insertArcRotation {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) : Equiv.Perm (ArcDart E) :=
  ((Equiv.swap (.inl da) (.inr false)).trans (Equiv.swap (.inl db) (.inr true))).trans
    (Equiv.sumCongr R.next (Equiv.refl Bool))

theorem insertArcRotation_alpha {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) :
    insertArcRotation R da db (.inl da) = .inr false := by
  simp [insertArcRotation, Equiv.swap_apply_def]

theorem insertArcRotation_beta {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (hne : db ≠ da) :
    insertArcRotation R da db (.inl db) = .inr true := by
  simp [insertArcRotation, Equiv.swap_apply_def,hne]

theorem insertArcRotation_arc_false {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (hne : da ≠ db) :
    insertArcRotation R da db (.inr false) = .inl (R.next da) := by
  simp [insertArcRotation, Equiv.swap_apply_def,hne]

theorem insertArcRotation_arc_true {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) :
    insertArcRotation R da db (.inr true) = .inl (R.next db) := by
  simp [insertArcRotation, Equiv.swap_apply_def]

theorem insertArcRotation_other {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db d : Dart E) (ha : d ≠ da) (hb : d ≠ db) :
    insertArcRotation R da db (.inl d) = .inl (R.next d) := by
  simp [insertArcRotation,Equiv.swap_apply_def,ha,hb]

theorem arcTail_insertArcRotation {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (d : ArcDart E) :
    arcTail a b alpha beta (insertArcRotation R da db d) = arcTail a b alpha beta d := by
  have hdab : da ≠ db := by intro h; rw [h,hb] at ha; exact hne ha.symm
  cases d with
  | inl d =>
    by_cases hda : d = da
    · subst d; rw [insertArcRotation_alpha]; exact ha.symm
    by_cases hdb : d = db
    · subst d; rw [insertArcRotation_beta R da db hdab.symm]; exact hb.symm
    · rw [insertArcRotation_other R da db d hda hdb]
      exact R.tail_next d
  | inr d => cases d with
    | false => rw [insertArcRotation_arc_false R da db hdab]; exact (R.tail_next da).trans ha
    | true => rw [insertArcRotation_arc_true]; exact (R.tail_next db).trans hb

noncomputable def arcFaceNext {V E : Type*} {a b : E → V} (R : EdgeRotation a b) (da db : Dart E) :
    Equiv.Perm (ArcDart E) := (arcReverse E).trans (insertArcRotation R da db)

/-- Actual augmented face orbits, before any genus-zero or distinct-exterior-face theorem. -/
abbrev ArcFace {V E : Type*} {a b : E → V} (R : EdgeRotation a b) (da db : Dart E) :=
  Quotient (Equiv.Perm.SameCycle.setoid (arcFaceNext R da db))

noncomputable instance {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) : Fintype (ArcFace R da db) := Fintype.ofFinite _

noncomputable def arcLeftFace {V E : Type*} {a b : E → V} (R : EdgeRotation a b) (da db : Dart E)
    (d : ArcDart E) : ArcFace R da db := Quotient.mk _ d

noncomputable def arcRightFace {V E : Type*} {a b : E → V} (R : EdgeRotation a b) (da db : Dart E)
    (d : ArcDart E) : ArcFace R da db := arcLeftFace R da db (arcReverse E d)

theorem arcReverse_arcReverse {E : Type*} (d : ArcDart E) : arcReverse E (arcReverse E d) = d := by
  cases d with
  | inl d => simp [arcReverse]
  | inr d => simp [arcReverse]

theorem arcLeftFace_next {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (da db : Dart E) (d : ArcDart E) :
    arcLeftFace R da db (insertArcRotation R da db d) = arcRightFace R da db d := by
  have h : arcLeftFace R da db (arcFaceNext R da db (arcReverse E d)) =
      arcLeftFace R da db (arcReverse E d) := by
    apply Quotient.sound
    exact (show (arcFaceNext R da db).SameCycle (arcReverse E d)
      (arcFaceNext R da db (arcReverse E d)) from ⟨1,by simp⟩).symm
  simpa only [arcFaceNext,Equiv.trans_apply,arcReverse_arcReverse,arcRightFace] using h

/-- The arc closes the flow. Its assigned current is not a voltage-gradient conductance. -/
def arcCurrent {V E : Type*} (a b : E → V) (phi : V → ℝ) (M : ℝ) : ArcDart E → ℝ
  | .inl d => current a b phi d
  | .inr false => M
  | .inr true => -M

theorem arcCurrent_reverse {V E : Type*} (a b : E → V) (phi : V → ℝ) (M : ℝ)
    (d : ArcDart E) : arcCurrent a b phi M (arcReverse E d) = -arcCurrent a b phi M d := by
  cases d with
  | inl d => simp [arcReverse,arcCurrent]
  | inr d => cases d <;> simp [arcReverse,arcCurrent]

noncomputable def arcDivergence {V E : Type*} [Fintype E] (a b : E → V)
    (alpha beta : V) (phi : V → ℝ) (M : ℝ) (x : V) : ℝ :=
  ∑ d : ArcDart E, if arcTail a b alpha beta d = x then arcCurrent a b phi M d else 0

theorem arcDivergence_eq {V E : Type*} [Fintype E] (a b : E → V)
    (alpha beta : V) (phi : V → ℝ) (M : ℝ) (x : V) :
    arcDivergence a b alpha beta phi M x =
      laplacian a b phi x + (if alpha = x then M else 0)+(if beta = x then -M else 0) := by
  simp only [arcDivergence,Fintype.sum_sum_type,Fintype.sum_bool,arcTail,arcCurrent]
  rw [← divergence_eq_laplacian]
  unfold divergence
  ring

/-- Terminal flux is derived from the literal original energy, with its positive Laplacian sign. -/
theorem terminal_flux_eq_energy {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (phi : V → ℝ) (alpha beta : V) (hne : alpha ≠ beta)
    (ha : phi alpha = 0) (hb : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    laplacian a b phi alpha = -energy a b phi ∧ laplacian a b phi beta = energy a b phi := by
  have hpoint : ∀ x, phi x*laplacian a b phi x = if x = beta then laplacian a b phi beta else 0 := by
    intro x
    by_cases hxb : x = beta
    · subst x; simp [hb]
    by_cases hxa : x = alpha
    · subst x; simp [ha,hne]
    · simp [hh x hxa hxb,hxb]
  have henergy := energy_eq_incidence_sum a b phi
  simp only [hpoint,Finset.sum_ite_eq',Finset.mem_univ,if_true] at henergy
  have hpoint' : ∀ x, laplacian a b phi x =
      (if x = alpha then laplacian a b phi alpha else 0)+(if x = beta then laplacian a b phi beta else 0) := by
    intro x
    by_cases hxa : x = alpha
    · subst x; simp [hne]
    by_cases hxb : x = beta
    · subst x; simp [hne.symm]
    · simp [hh x hxa hxb,hxa,hxb]
  have hsum := sum_laplacian_eq_zero a b phi
  rw [Finset.sum_congr rfl (fun x _ => hpoint' x),Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at hsum
  exact ⟨by linarith only [henergy,hsum],henergy.symm⟩

/-- Every augmented vertex is balanced; no response or stream conclusion is assumed. -/
theorem arcDivergence_eq_zero {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (phi : V → ℝ) (alpha beta : V) (hne : alpha ≠ beta)
    (ha : phi alpha = 0) (hb : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) (x : V) :
    arcDivergence a b alpha beta phi (energy a b phi) x = 0 := by
  rw [arcDivergence_eq]
  have hf := terminal_flux_eq_energy a b phi alpha beta hne ha hb hh
  by_cases hxa : x = alpha
  · subst x; simp [hf.1,hne.symm]
  by_cases hxb : x = beta
  · subst x; simp [hf.2,hne]
  · simp [hh x hxa hxb,Ne.symm hxa,Ne.symm hxb]

end FiniteAvalanches.Electrical.Plane
