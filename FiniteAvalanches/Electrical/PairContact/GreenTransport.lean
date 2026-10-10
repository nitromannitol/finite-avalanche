import FiniteAvalanches.Electrical.PairContact.DeterminantAlgebra
import FiniteAvalanches.Electrical.Green.Pendant

/-! Six fresh terminals: exact actual resistance-minor transport, with the original ground. -/
namespace FiniteAvalanches.Electrical.PairFormula
open Polynomial
open scoped Classical
noncomputable section

private theorem coeff_triple (a b c : ℝ) :
    ((X-C a)*(X-C b)*(X-C c)).coeff 1 = a*b+a*c+b*c := by
  have h : (X-C a)*(X-C b)*(X-C c) =
      X^3-C (a+b+c)*X^2+C (a*b+a*c+b*c)*X-C (a*b*c) := by
    simp only [map_add,map_mul]
    ring
  rw [h]
  simp only [coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_C]
  norm_num

/-- Row and column offsets cancel in the literal coefficient of t. -/
theorem minor_coeff_add_rows_columns (R : Fin 3 → Fin 3 → ℝ) (a b : Fin 3 → ℝ) :
    ((Matrix.of fun i j : Fin 3 => (X : Polynomial ℝ)-C (R i j+a i+b j)).det).coeff 1 =
      ((Matrix.of fun i j : Fin 3 => (X : Polynomial ℝ)-C (R i j)).det).coeff 1 := by
  rw [Matrix.det_fin_three,Matrix.det_fin_three]
  simp only [Matrix.of_apply,coeff_add,coeff_sub,coeff_triple]
  ring

/-- All six fresh leaf terminals preserve each full resistance minor, even at coincident roots.
Only the proved unit resistance of each fresh diagonal is used; the ground stays original. -/
theorem all_six_minor_coeff {V E : Type} [Fintype V] [Fintype E]
    (a b : E → V) (hc : (supportGraph a b).Preconnected) (x : Fin 6 → V)
    (U W : Fin 3 → Fin 6) (hd : Disjoint (Set.range U) (Set.range W)) :
    let G := groundedGreen a b (x 0) hc
    let H := groundedGreen (pendantLeft a x) (pendantRight b) (Sum.inl (x 0))
      (pendant_preconnected a b x hc)
    ((Matrix.of fun r s : Fin 3 => (X : Polynomial ℝ)-C
      ((H (Sum.inr (U r)) (Sum.inr (U r))+H (Sum.inr (W s)) (Sum.inr (W s))-
        2*H (Sum.inr (U r)) (Sum.inr (W s)))/2)).det).coeff 1 =
    ((Matrix.of fun r s : Fin 3 => (X : Polynomial ℝ)-C
      ((G (x (U r)) (x (U r))+G (x (W s)) (x (W s))-
        2*G (x (U r)) (x (W s)))/2)).det).coeff 1 := by
  intro G H
  have hcross (r s : Fin 3) : W s ≠ U r := by
    intro h
    exact Set.disjoint_left.mp hd ⟨r,rfl⟩ ⟨s,h⟩
  have diag (k : Fin 6) : H (Sum.inr k) (Sum.inr k) = G (x k) (x k)+1 := by
    simpa using groundedGreen_pendant_leaf_leaf a b x (x 0) hc k k
  have cross (r s : Fin 3) : H (Sum.inr (U r)) (Sum.inr (W s)) =
      G (x (U r)) (x (W s)) := by
    simpa only [if_neg (hcross r s),add_zero] using
      groundedGreen_pendant_leaf_leaf a b x (x 0) hc (U r) (W s)
  have heq : (Matrix.of fun r s : Fin 3 => (X : Polynomial ℝ)-C
      ((H (Sum.inr (U r)) (Sum.inr (U r))+H (Sum.inr (W s)) (Sum.inr (W s))-
        2*H (Sum.inr (U r)) (Sum.inr (W s)))/2)) =
      Matrix.of (fun r s : Fin 3 => (X : Polynomial ℝ)-C
        ((G (x (U r)) (x (U r))+G (x (W s)) (x (W s))-
          2*G (x (U r)) (x (W s)))/2+1+0)) := by
    funext r s
    simp only [Matrix.of_apply,diag,cross]
    apply congrArg (fun t : ℝ => (X : Polynomial ℝ)-C t)
    ring
  rw [heq]
  exact minor_coeff_add_rows_columns _ (fun _ => 1) (fun _ => 0)

end
end FiniteAvalanches.Electrical.PairFormula
