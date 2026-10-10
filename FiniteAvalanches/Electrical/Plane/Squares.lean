import FiniteAvalanches.Electrical.Plane.AuxiliaryArc
import FiniteAvalanches.Electrical.Geometry.BoundaryMidpoints

/-! Literal coordinate adapters on actual augmented face orbits.
These do not construct a normalized electrical stream function or assert a tiling. -/
namespace FiniteAvalanches.Electrical.Plane

open Set
open scoped BigOperators Classical
open FiniteAvalanches.Electrical.Geometry

/-- The actual voltage interval times the actual adjacent-face interval. -/
noncomputable def potentialRectangle {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (d : Dart E) : Set (ℝ × ℝ) :=
  rectangle (min (phi (tail a b d)) (phi (head a b d)))
    (max (phi (tail a b d)) (phi (head a b d)))
    (min (psi (arcLeftFace R da db (.inl d))) (psi (arcRightFace R da db (.inl d))))
    (max (psi (arcLeftFace R da db (.inl d))) (psi (arcRightFace R da db (.inl d))))

private theorem min_add_abs_sub (u v : ℝ) : min u v+|u-v| = max u v := by
  rcases le_total u v with h | h
  · rw [min_eq_left h,max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h,max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]; ring

/-- Convert one actual electrical stream increment to its closed square.
The proof input is a local coordinate identity, not a tiling or packing estimate. -/
noncomputable def incrementSquare {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (d : Dart E)
    (_h : psi (arcLeftFace R da db (.inl d))-psi (arcRightFace R da db (.inl d)) = current a b phi d) : Square where
  x := min (phi (tail a b d)) (phi (head a b d))
  y := min (psi (arcLeftFace R da db (.inl d))) (psi (arcRightFace R da db (.inl d)))
  side := |current a b phi d|
  side_nonneg := abs_nonneg _

/-- The conversion exactly preserves both voltage and stream intervals. -/
theorem incrementSquare_carrier {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (d : Dart E)
    (h : psi (arcLeftFace R da db (.inl d))-psi (arcRightFace R da db (.inl d)) = current a b phi d) :
    (incrementSquare R da db phi psi d h).carrier = potentialRectangle R da db phi psi d := by
  dsimp [incrementSquare,Square.carrier,potentialRectangle,rectangle]
  rw [← h, min_add_abs_sub]
  rw [h]
  rw [current, min_add_abs_sub]

/-- Midpoints on the two sides are derived from the electrical coordinates, not chosen plane points. -/
noncomputable def sideMidpoint {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (d : Dart E) : ℝ × ℝ :=
  (phi (tail a b d), (psi (arcLeftFace R da db (.inl d))+psi (arcRightFace R da db (.inl d)))/2)

private theorem midpoint_mem_Icc (u v : ℝ) : (u+v)/2 ∈ Icc (min u v) (max u v) := by
  constructor
  · linarith [min_le_left u v,min_le_right u v]
  · linarith [le_max_left u v,le_max_right u v]

theorem sideMidpoint_mem {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (d : Dart E)
    (h : psi (arcLeftFace R da db (.inl d))-psi (arcRightFace R da db (.inl d)) = current a b phi d) :
    sideMidpoint R da db phi psi d ∈ (incrementSquare R da db phi psi d h).carrier := by
  rw [incrementSquare_carrier]
  exact ⟨⟨min_le_left _ _,le_max_left _ _⟩,midpoint_mem_Icc _ _⟩

theorem oppositeMidpoint_mem {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (d : Dart E)
    (h : psi (arcLeftFace R da db (.inl d))-psi (arcRightFace R da db (.inl d)) = current a b phi d) :
    (phi (head a b d), (psi (arcLeftFace R da db (.inl d))+psi (arcRightFace R da db (.inl d)))/2)
      ∈ (incrementSquare R da db phi psi d h).carrier := by
  rw [incrementSquare_carrier]
  exact ⟨⟨min_le_right _ _,le_max_right _ _⟩,midpoint_mem_Icc _ _⟩

/-- Zero current gives the source's one common voltage/stream point. -/
theorem incrementSquare_zero_current {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (d : Dart E)
    (h : psi (arcLeftFace R da db (.inl d))-psi (arcRightFace R da db (.inl d)) = current a b phi d)
    (hz : current a b phi d = 0) :
    (incrementSquare R da db phi psi d h).side = 0 ∧
      (incrementSquare R da db phi psi d h).carrier =
        {(phi (tail a b d),psi (arcLeftFace R da db (.inl d)))} := by
  have hv : phi (head a b d) = phi (tail a b d) := by unfold current at hz; linarith only [hz]
  have hf : psi (arcRightFace R da db (.inl d)) = psi (arcLeftFace R da db (.inl d)) := by
    rw [hz] at h
    linarith only [h]
  constructor
  · simp [incrementSquare,hz]
  · rw [incrementSquare_carrier]
    simp [potentialRectangle,rectangle,hv,hf]

/-- The own-square middle error remains in the comparison, including zero currents. -/
theorem midpoint_middle_error_le {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (d : Dart E)
    (h : psi (arcLeftFace R da db (.inl d))-psi (arcRightFace R da db (.inl d)) = current a b phi d)
    (epsilon y0 lambda : ℝ) (he : 0 < epsilon) (hl : 1 ≤ lambda) :
    |angular epsilon y0 (sideMidpoint R da db phi psi d)-angular epsilon y0
      (phi (head a b d), (psi (arcLeftFace R da db (.inl d))+psi (arcRightFace R da db (.inl d)))/2)| ≤
      (incrementSquare R da db phi psi d h).angularOsc epsilon y0 lambda hl he := by
  have hsub := (incrementSquare R da db phi psi d h).carrier_subset_dilate lambda hl
  exact abs_sub_le_oscillation (hsub (sideMidpoint_mem R da db phi psi d h))
    (hsub (oppositeMidpoint_mem R da db phi psi d h))
    ⟨1,fun z _ w _ => angular_sub_le_one epsilon y0 he z w⟩

/-- With clockwise rotation and left-minus-right physical-current convention,
stream increments around alpha are positive voltage increments. -/
theorem stream_increment_next {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (psi : ArcFace R da db → ℝ)
    (j : ArcDart E → ℝ) (d : ArcDart E)
    (h : psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = j d) :
    psi (arcLeftFace R da db (insertArcRotation R da db d))-psi (arcLeftFace R da db d) = -j d := by
  rw [arcLeftFace_next]
  linarith only [h]

/-- Normalizing the right exterior face to zero forces the other value to be M. -/
theorem exterior_stream_values {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (M : ℝ)
    (h : psi (arcLeftFace R da db (.inr false))-psi (arcRightFace R da db (.inr false)) =
      arcCurrent a b phi M (.inr false))
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) :
    psi (arcLeftFace R da db (.inr false)) = M := by
  change _ = M at h
  rw [h0,sub_zero] at h
  exact h

/-- The first original alpha incidence starts at zero, with no arbitrary offset. -/
theorem first_alpha_stream_eq_zero {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (hne : da ≠ db)
    (psi : ArcFace R da db → ℝ) (h0 : psi (arcRightFace R da db (.inr false)) = 0) :
    psi (arcLeftFace R da db (.inl (R.next da))) = 0 := by
  rw [← insertArcRotation_arc_false R da db hne,arcLeftFace_next,h0]

/-- The cumulative stream height follows the actual rotation orbit and signed currents. -/
theorem stream_height_along_rotation {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (psi : ArcFace R da db → ℝ)
    (j : ArcDart E → ℝ)
    (hj : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = j d)
    (d : ArcDart E) (n : ℕ) :
    psi (arcLeftFace R da db (((insertArcRotation R da db)^n) d)) =
      psi (arcLeftFace R da db d)-∑ k ∈ Finset.range n, j (((insertArcRotation R da db)^k) d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,Finset.sum_range_succ]
    have h := stream_increment_next R da db psi j (((insertArcRotation R da db)^n) d) (hj _)
    linarith only [ih,h]

/-- Total square area is the original once-counted energy; the auxiliary arc is excluded. -/
theorem sum_increment_square_area_eq_energy {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ)
    (h : ∀ d : Dart E, psi (arcLeftFace R da db (.inl d))-psi (arcRightFace R da db (.inl d)) = current a b phi d) :
    (∑ e : E, MeasureTheory.volume.real (incrementSquare R da db phi psi (e,false) (h _)).openCarrier) =
      energy a b phi := by
  simp only [Square.area_openCarrier,incrementSquare,current,tail,head,reverse]
  simp only [Bool.false_eq_true,↓reduceIte,sq_abs]
  rfl

end FiniteAvalanches.Electrical.Plane
