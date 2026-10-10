import FiniteAvalanches.Electrical.Plane.CutPaths
import FiniteAvalanches.Electrical.Plane.PathIntervals
import FiniteAvalanches.Electrical.Plane.Sides
import Mathlib.Topology.Order.DenselyOrdered

/-! Literal closed and open slices of actual voltage/stream squares, including zero-side squares. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- The open carrier is exactly the topological interior, also when side zero. -/
theorem Square.interior_carrier (Q : Square) : interior Q.carrier = Q.openCarrier := by
  simp only [Square.carrier,Square.openCarrier,interior_prod_eq,interior_Icc]

/-- Both actual coordinate intervals are preserved for open interiors as well. -/
theorem incrementSquare_openCarrier {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (d : Dart E)
    (hp : psi (arcLeftFace R da db (.inl d))-psi (arcRightFace R da db (.inl d)) = current a b phi d) :
    (incrementSquare R da db phi psi d hp).openCarrier =
      Set.Ioo (min (phi (tail a b d)) (phi (head a b d))) (max (phi (tail a b d)) (phi (head a b d))) ×ˢ
      Set.Ioo (min (psi (arcLeftFace R da db (.inl d))) (psi (arcRightFace R da db (.inl d))))
        (max (psi (arcLeftFace R da db (.inl d))) (psi (arcRightFace R da db (.inl d)))) := by
  rw [← Square.interior_carrier,incrementSquare_carrier]
  simp only [potentialRectangle,rectangle,interior_prod_eq,interior_Icc]

/-- Every actual crossing copy's horizontal voltage interval contains the threshold. -/
theorem cut_voltage_bounds {V E : Type*} [Fintype E]
    (a b : E → V) (phi : V → ℝ) (t : ℝ) (e : CutCopy a b phi t) :
    min (phi (a e.val)) (phi (b e.val)) ≤ t ∧ t ≤ max (phi (a e.val)) (phi (b e.val)) := by
  rcases (mem_crossingEdges a b phi t e.val).mp e.property with hm | hm
  · exact ⟨(min_le_left _ _).trans hm.1.le,hm.2.trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans hm.1.le,hm.2.trans (le_max_left _ _)⟩

/-- A strict interior voltage slice of an original copy makes it an actual cut-copy ID. -/
theorem mem_crossingEdges_of_voltage_interior {V E : Type*} [Fintype E]
    (a b : E → V) (phi : V → ℝ) (t : ℝ) (e : E)
    (ht : min (phi (a e)) (phi (b e)) < t ∧ t < max (phi (a e)) (phi (b e))) :
    e ∈ crossingEdges a b phi t := by
  rcases le_total (phi (a e)) (phi (b e)) with h | h
  · rw [min_eq_left h,max_eq_right h] at ht
    exact (mem_crossingEdges a b phi t e).mpr (Or.inl ⟨ht.1,ht.2.le⟩)
  · rw [min_eq_right h,max_eq_left h] at ht
    exact (mem_crossingEdges a b phi t e).mpr (Or.inr ⟨ht.1,ht.2.le⟩)

/-- Orienting a crossing original copy leaves its actual closed rectangle unchanged. -/
theorem cut_rectangle_eq_original {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (t : ℝ)
    (psi : ArcFace R da db → ℝ) (e : CutCopy a b phi t) :
    potentialRectangle R da db phi psi (cutDart a b phi t e) =
      potentialRectangle R da db phi psi (e.val,false) := by
  by_cases h : phi (a e.val) < t
  · simp only [cutDart,if_pos h]
    exact potentialRectangle_reverse R da db phi psi (e.val,false)
  · simp only [cutDart,if_neg h]

/-- The actual closed slice is the interval between the path copy's ascending stream values. -/
theorem cut_square_slice {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (M t : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (e : CutCopy a b phi t) (u : ℝ) :
    (t,u) ∈ (incrementSquare R da db phi psi (e.val,false) (hp (.inl (e.val,false)))).carrier ↔
      psi (cutA R da db phi t e) ≤ u ∧ u ≤ psi (cutB R da db phi t e) := by
  rw [incrementSquare_carrier,← cut_rectangle_eq_original R da db phi t psi e]
  have hi := cut_stream_increasing R da db phi M t psi hp e
  have hv := cut_voltage_bounds a b phi t e
  change (_ ∧ _) ↔ _
  have hvol : t ∈ Set.Icc (min (phi (tail a b (cutDart a b phi t e))) (phi (head a b (cutDart a b phi t e))))
      (max (phi (tail a b (cutDart a b phi t e))) (phi (head a b (cutDart a b phi t e)))) := by
    by_cases h : phi (a e.val) < t
    · rw [cutDart,if_pos h]
      change min (phi (b e.val)) (phi (a e.val)) ≤ t ∧ t ≤ max (phi (b e.val)) (phi (a e.val))
      simpa only [min_comm,max_comm] using hv
    · rw [cutDart,if_neg h]
      exact hv
  change (_ ∧ u ∈ Set.Icc (min (psi (cutB R da db phi t e)) (psi (cutA R da db phi t e)))
    (max (psi (cutB R da db phi t e)) (psi (cutA R da db phi t e)))) ↔ _
  rw [min_eq_right hi.le,max_eq_left hi.le]
  exact and_iff_right hvol

end FiniteAvalanches.Electrical.Plane
