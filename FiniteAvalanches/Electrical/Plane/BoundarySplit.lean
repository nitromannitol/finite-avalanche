import FiniteAvalanches.Electrical.Plane.TerminalIntervals
import FiniteAvalanches.Electrical.Plane.Tiling
import FiniteAvalanches.Electrical.SplitTerminal

/-! The literal ordered split keeps original copy IDs and exact cumulative electrical coordinates. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- At a loopless vertex an original copy has exactly one outgoing incidence. -/
theorem incidence_copy_injective {V E : Type*} {a b : E → V}
    (alpha : V) (he : ∀ e, a e ≠ b e) :
    Function.Injective (fun z : Incidences a b alpha => z.val.1) := by
  rintro ⟨⟨e,c⟩,hc⟩ ⟨⟨f,d⟩,hd⟩ h
  change e = f at h
  subst f
  apply Subtype.ext
  cases c <;> cases d
  · rfl
  · exact (he e (hc.trans hd.symm)).elim
  · exact (he e (hd.trans hc.symm)).elim
  · rfl

/-- The upper terminal receives exactly the original copies in the upper ordered interval.
Nonincident copies are absent from this literal set and their endpoints remain unchanged. -/
noncomputable def orderedSide {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (k : ℕ) (e : E) : Bool :=
  decide (∃ i : Fin (incidenceCount a b alpha),
    (alphaEnumeration R alpha beta hne da db ha hb i).val.1 = e ∧ k ≤ i.val)

theorem orderedSide_enumeration {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (he : ∀ e, a e ≠ b e)
    (k : ℕ) (i : Fin (incidenceCount a b alpha)) :
    orderedSide R alpha beta hne da db ha hb k
      (alphaEnumeration R alpha beta hne da db ha hb i).val.1 = true ↔ k ≤ i.val := by
  simp only [orderedSide,decide_eq_true_eq]
  constructor
  · rintro ⟨j,hji,hj⟩
    have h := incidence_copy_injective alpha he hji
    have hij := (alphaEnumeration R alpha beta hne da db ha hb).injective h
    simpa only [hij] using hj
  · intro hi
    exact ⟨i,rfl,hi⟩

/-- The midpoint of each original alpha side is its actual cumulative interval midpoint. -/
theorem alpha_midpoint_coordinates {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (hpa : phi alpha = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi (energy a b phi) z)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) (i : Fin (incidenceCount a b alpha)) :
    sideMidpoint R da db phi psi (alphaEnumeration R alpha beta hne da db ha hb i).val =
      (0,boundaryHeight (alphaCurrentSequence R alpha beta hne da db ha hb phi) i.val +
        alphaCurrentSequence R alpha beta hne da db ha hb phi i/2) := by
  obtain ⟨hl,hr⟩ := alpha_stream_interval R alpha beta hne da db ha hb phi hpa psi hp h0 i
  dsimp only [sideMidpoint]
  rw [(alphaEnumeration R alpha beta hne da db ha hb i).property,hpa,hl,hr]
  congr 1
  ring

/-- The all-index midpoint refinement is consumed on actual incident electrical coordinates. -/
theorem alpha_midpoint_value {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (hpa : phi alpha = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi (energy a b phi) z)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0)
    (hs : ∀ i, 0 < alphaCurrentSequence R alpha beta hne da db ha hb phi i)
    (j0 j1 : Fin (incidenceCount a b alpha)) (hj : j0.val+1 = j1.val)
    (i : Fin (incidenceCount a b alpha)) :
    let s := alphaCurrentSequence R alpha beta hne da db ha hb phi
    let epsilon := min (s j0) (s j1)/10
    angular epsilon (boundaryHeight s j1.val)
      (sideMidpoint R da db phi psi (alphaEnumeration R alpha beta hne da db ha hb i).val) =
      if i.val < j1.val then 0 else 1 := by
  intro s epsilon
  have he : 0 < epsilon := div_pos (lt_min (hs j0) (hs j1)) (by norm_num)
  rw [alpha_midpoint_coordinates R alpha beta hne da db ha hb phi hpa psi hp h0 i]
  apply boundary_axis_midpoint s (fun i => (hs i).le) j0 j1 hj epsilon he
  · dsimp only [epsilon]
    have h := min_le_left (s j0) (s j1)
    have hn := (hs j0).le
    linarith only [h,hn]
  · dsimp only [epsilon]
    have h := min_le_right (s j0) (s j1)
    have hn := (hs j1).le
    linarith only [h,hn]

end FiniteAvalanches.Electrical.Plane
