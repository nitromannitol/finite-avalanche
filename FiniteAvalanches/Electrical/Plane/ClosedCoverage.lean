import FiniteAvalanches.Electrical.Plane.SquareIntervals

/-! Finite closed-square unions retain all boundary limits of the proved interior-voltage slices. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- The actual closed square includes its zero-side singleton and is a closed set. -/
theorem Square.isClosed_carrier (Q : Square) : IsClosed Q.carrier := isClosed_Icc.prod isClosed_Icc

/-- The actual square union covers the full closed rectangle, including both voltage boundaries. -/
theorem rectangle_subset_square_union {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hface : R.rightFace da = R.rightFace db)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (M : ℝ) (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) :
    rectangle 0 1 0 M ⊆ ⋃ e : E,
      (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).carrier := by
  let U : Set (ℝ × ℝ) := ⋃ e : E, (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).carrier
  have hU : IsClosed U := isClosed_iUnion_of_finite
    (fun e => Square.isClosed_carrier (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))))
  have hI : Set.Ioo (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) M ⊆ U := by
    intro z hz
    obtain ⟨e,he⟩ := square_slice_cover R alpha beta hne da db ha hb hface phi hp0 hp1 M psi hp h0
      z.1 z.2 hz.1.1 hz.1.2 hz.2.1 hz.2.2
    exact Set.mem_iUnion.mpr ⟨e,he⟩
  have hc : closure (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) M) = rectangle 0 1 0 M := by
    rw [closure_prod_eq,closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),isClosed_Icc.closure_eq]
    rfl
  rw [← hc]
  exact closure_minimal hI hU

/-- All original squares together equal the literal normalized rectangle, with no coverage premise. -/
theorem square_union_eq_rectangle {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected) (hface : R.rightFace da = R.rightFace db)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi (energy a b phi) d)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) :
    (⋃ e : E, (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).carrier) =
      rectangle 0 1 0 (energy a b phi) := by
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro e
    exact incrementSquare_subset_rectangle R alpha beta hne da db ha hb hc phi hp0 hp1 hh psi hp h0 (e,false)
  · exact rectangle_subset_square_union R alpha beta hne da db ha hb hface phi hp0 hp1
      (energy a b phi) psi hp h0

end FiniteAvalanches.Electrical.Plane
