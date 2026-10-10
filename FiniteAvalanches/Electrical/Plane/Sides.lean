import FiniteAvalanches.Electrical.Plane.Segments

/-! Actual incident square sides and zero-current points lie in the vertex segment. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical

/-- Reversing an original copied dart changes neither coordinate interval. -/
theorem potentialRectangle_reverse {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (da db : Dart E) (phi : V → ℝ) (psi : ArcFace R da db → ℝ) (d : Dart E) :
    potentialRectangle R da db phi psi (reverse E d) = potentialRectangle R da db phi psi d := by
  have hl : arcLeftFace R da db (.inl (reverse E d)) = arcRightFace R da db (.inl d) := rfl
  have hr : arcRightFace R da db (.inl (reverse E d)) = arcLeftFace R da db (.inl d) := by
    change arcLeftFace R da db (arcReverse E (arcReverse E (.inl d))) = _
    rw [arcReverse_arcReverse]
  simp only [potentialRectangle,tail_reverse,head_reverse,hl,hr,min_comm,max_comm]

/-- Every whole incident side at the vertex voltage is in its actual min/max segment. -/
theorem incidentSquare_side_subset {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (M : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (x : V) (hx0 : x ≠ alpha) (hx1 : x ≠ beta) (hx : (incidenceDarts a b x).Nonempty)
    (d : Dart E) (hd : tail a b d = x ∨ head a b d = x) :
    ∀ z ∈ (incrementSquare R da db phi psi d (hp (.inl d))).carrier,
      z.1 = phi x → z ∈ vertexSegment R da db phi psi x hx := by
  have atTail (e : Dart E) (he : tail a b e = x) (z : ℝ × ℝ)
      (hz : z ∈ potentialRectangle R da db phi psi e) (hzx : z.1 = phi x) :
      z ∈ vertexSegment R da db phi psi x hx := by
    have hl := incident_left_bounds R da db psi x hx e he
    have hr := incident_right_bounds R alpha beta da db ha hb psi x hx0 hx1 hx e he
    change _ ∧ z.2 ∈ Set.Icc _ _ at hz
    change z.1 ∈ Set.Icc (phi x) (phi x) ∧ z.2 ∈ Set.Icc _ _
    exact ⟨⟨hzx.ge,hzx.le⟩,⟨(le_min hl.1 hr.1).trans hz.2.1,
      hz.2.2.trans (max_le hl.2 hr.2)⟩⟩
  intro z hz hzx
  rw [incrementSquare_carrier] at hz
  rcases hd with hd | hd
  · exact atTail d hd z hz hzx
  · apply atTail (reverse E d) hd z _ hzx
    rw [potentialRectangle_reverse]
    exact hz

/-- A zero-current original copy gives the same point in each free endpoint segment. -/
theorem zero_current_point_mem_segment {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (M : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (x : V) (hx0 : x ≠ alpha) (hx1 : x ≠ beta) (hx : (incidenceDarts a b x).Nonempty)
    (d : Dart E) (hd : tail a b d = x ∨ head a b d = x) (hz : current a b phi d = 0) :
    (phi (tail a b d),psi (arcLeftFace R da db (.inl d))) ∈ vertexSegment R da db phi psi x hx := by
  have hQ := (incrementSquare_zero_current R da db phi psi d (hp (.inl d)) hz).2
  apply incidentSquare_side_subset R alpha beta da db ha hb phi M psi hp x hx0 hx1 hx d hd
  · rw [hQ]
    exact Set.mem_singleton _
  · change phi (tail a b d) = phi x
    rcases hd with hd | hd
    · rw [hd]
    · have hv := sub_eq_zero.mp hz
      exact hv.trans (congrArg phi hd)

end FiniteAvalanches.Electrical.Plane
