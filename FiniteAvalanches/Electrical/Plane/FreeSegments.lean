import FiniteAvalanches.Electrical.Plane.TrialResponse

/-! Actual free-vertex midpoint assignments, maximal positive copy choices, and zero-current points. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

private theorem min_add_abs_sub_eq_max (u v : ℝ) : min u v+|u-v| = max u v := by
  rcases le_total u v with h | h
  · rw [min_eq_left h,max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h,max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]; ring

/-- Reorientation preserves the square itself, not just its closed carrier. -/
theorem incrementSquare_eq_original {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (psi : ArcFace R da db → ℝ)
    (M : ℝ) (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi M z)
    (z : Dart E) :
    incrementSquare R da db phi psi z (hp (.inl z)) =
      incrementSquare R da db phi psi (z.1,false) (hp (.inl (z.1,false))) := by
  rcases z with ⟨e,c⟩
  cases c with
  | false => rfl
  | true =>
    have hl : arcLeftFace R da db (.inl (e,true)) = arcRightFace R da db (.inl (e,false)) := rfl
    have hr : arcRightFace R da db (.inl (e,true)) = arcLeftFace R da db (.inl (e,false)) := by
      change arcLeftFace R da db (arcReverse E (arcReverse E (.inl (e,false)))) = _
      rw [arcReverse_arcReverse]
    have ht : tail a b (e,true) = b e := rfl
    have hh : head a b (e,true) = a e := rfl
    have ht' : tail a b (e,false) = a e := rfl
    have hh' : head a b (e,false) = b e := rfl
    simp only [incrementSquare,current,ht,hh,ht',hh',hl,hr,min_comm,abs_sub_comm]

/-- The maximal incident original square contains the complete actual segment after the source dilation. -/
theorem vertexSegment_subset_max_dilate {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (M : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi M z)
    (x : V) (hx0 : x ≠ alpha) (hx1 : x ≠ beta) (hx : (incidenceDarts a b x).Nonempty)
    (d : ℝ) (hd : 1 ≤ d) (hdeg : degree a b x ≤ d)
    (z : Dart E) (hz : tail a b z = x) (hmax : |current a b phi z| = largestCurrent a b phi x hx) :
    vertexSegment R da db phi psi x hx ⊆
      ((incrementSquare R da db phi psi (z.1,false) (hp (.inl (z.1,false)))).dilate (2*d+3) (by linarith)).carrier := by
  let Q := incrementSquare R da db phi psi z (hp (.inl z))
  have hl := incident_left_bounds R da db psi x hx z hz
  have hr := incident_right_bounds R alpha beta da db ha hb psi x hx0 hx1 hx z hz
  have hspan := stream_span_le_degree_mul R alpha beta da db ha hb phi M psi hp x hx0 hx1 hx d hdeg
  have hqx : phi x = Q.x ∨ phi x = Q.x+Q.side := by
    have he := min_add_abs_sub_eq_max (phi (tail a b z)) (phi (head a b z))
    change phi x = min (phi (tail a b z)) (phi (head a b z)) ∨
      phi x = min (phi (tail a b z)) (phi (head a b z))+|phi (tail a b z)-phi (head a b z)|
    rw [he,hz]
    rcases le_total (phi x) (phi (head a b z)) with h | h
    · exact Or.inl (min_eq_left h).symm
    · exact Or.inr (max_eq_left h).symm
  have hQtop : Q.y+Q.side = max (psi (arcLeftFace R da db (.inl z))) (psi (arcRightFace R da db (.inl z))) := by
    have hj := hp (.inl z)
    change _ = current a b phi z at hj
    change min _ _+|current a b phi z| = _
    rw [← hj]
    exact min_add_abs_sub_eq_max _ _
  have hs : Q.side = largestCurrent a b phi x hx := hmax
  have hsub := segment_subset_dilate Q d (streamMin R da db psi x hx) (streamMax R da db psi x hx)
    (phi x) hd hqx (le_min hl.1 hr.1) (by rw [hQtop]; exact max_le hl.2 hr.2)
    (by rw [hs]; exact hspan)
  intro p hpseg
  have hpm : p.1 = phi x ∧ streamMin R da db psi x hx ≤ p.2 ∧ p.2 ≤ streamMax R da db psi x hx := by
    exact ⟨le_antisymm hpseg.1.2 hpseg.1.1,hpseg.2⟩
  have hpQ := hsub hpm
  dsimp only [Q] at hpQ
  rw [incrementSquare_eq_original R da db phi psi M hp z] at hpQ
  exact hpQ

/-- A positive-current free vertex has a genuine maximal original copy before any selection. -/
theorem exists_positive_max_square {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (M : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi M z)
    (x : V) (hx0 : x ≠ alpha) (hx1 : x ≠ beta) (hx : (incidenceDarts a b x).Nonempty)
    (d : ℝ) (hd : 1 ≤ d) (hdeg : degree a b x ≤ d) (hpos : 0 < largestCurrent a b phi x hx) :
    ∃ e : E, (a e = x ∨ b e = x) ∧
      (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).side = largestCurrent a b phi x hx ∧
      0 < (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).side ∧
      vertexSegment R da db phi psi x hx ⊆
        ((incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).dilate (2*d+3) (by linarith)).carrier := by
  obtain ⟨z,hz,hmax⟩ := exists_incident_max_current a b phi x hx
  have hs : (incrementSquare R da db phi psi (z.1,false) (hp (.inl (z.1,false)))).side = largestCurrent a b phi x hx := by
    rw [← incrementSquare_eq_original R da db phi psi M hp z]
    exact hmax
  refine ⟨z.1,?_,hs,hs ▸ hpos,vertexSegment_subset_max_dilate R alpha beta da db ha hb phi M psi hp
    x hx0 hx1 hx d hd hdeg z hz hmax⟩
  rcases z with ⟨e,c⟩
  cases c with
  | false => exact Or.inl hz
  | true => exact Or.inr hz

/-- At a zero-current free vertex the literal midpoint assignment has no endpoint error. -/
theorem zero_free_midpoint_eq {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (M : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi M z)
    (x : V) (hx0 : x ≠ alpha) (hx1 : x ≠ beta) (hx : (incidenceDarts a b x).Nonempty)
    (hzero : largestCurrent a b phi x hx = 0) (p : ℝ × ℝ)
    (hpm : p ∈ vertexSegment R da db phi psi x hx) :
    vertexMidpoint R da db phi psi x hx = p := by
  have hseg := vertexSegment_zero_current R alpha beta da db ha hb phi M psi hp x hx0 hx1 hx hzero
  have hm := vertexMidpoint_mem R da db phi psi x hx
  rw [hseg,Set.mem_singleton_iff] at hm hpm
  exact hm.trans hpm.symm

end FiniteAvalanches.Electrical.Plane
