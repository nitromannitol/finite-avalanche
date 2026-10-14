import CurrentSource.RegularCornerTransfer
import FiniteAvalanches.Electrical.Geometry.BoundaryMidpoints
import FiniteAvalanches.Electrical.Plane.SplitFormation

/-! The minimum-face trial and corner charging on every original copied split edge. -/

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Geometry
open CurrentRegularPhysical
open scoped Classical BigOperators
noncomputable section

variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)

/-- The current trial takes the minimum face at regular vertices and the prescribed terminal values. -/
def splitMinimumTrial (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) : SplitVertex (alpha D P) → ℝ
  | .inl x => if x.val = beta D P then 0 else
      angular epsilon y0 (minimumPoint D P marked Q A phi psi x.val)
  | .inr k => if k then 1 else 0

theorem splitMinimumTrial_range (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) (hepsilon : 0 < epsilon)
    (v : SplitVertex (alpha D P)) :
    0 ≤ splitMinimumTrial D P marked Q A phi psi epsilon y0 v ∧
      splitMinimumTrial D P marked Q A phi psi epsilon y0 v ≤ 1 := by
  cases v with
  | inl x =>
    dsimp only [splitMinimumTrial]
    split_ifs
    · norm_num
    · exact angular_mem_unitInterval epsilon y0 hepsilon _
  | inr k => cases k <;> norm_num [splitMinimumTrial]

/-- Given the separate terminal placement, the actual minimum-face trial has transfer constant 21.
The placement records only heights of original terminal corners; the endpoint comparisons,
regular minimum faces, six-neighbor count and voltage bounds are all produced internally. -/
theorem source_split_transfer21_of_terminal_corners
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (psi : A.embedding.Face → ℝ)
    (side : Copy D P marked → Bool) (exception : Copy D P marked)
    (epsilon y0 : ℝ) (hepsilon : 0 < epsilon)
    (hheight : ∀ e, e ≠ exception →
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P →
      if side e then y0 + epsilon ≤ max (psi (A.embedding.leftFace (.inl e)))
        (psi (A.embedding.rightFace (.inl e)))
      else min (psi (A.embedding.leftFace (.inl e)))
        (psi (A.embedding.rightFace (.inl e))) ≤ y0 - epsilon) :
    let phi := Repair8.voltage D P hD marked
    let f := splitMinimumTrial D P marked Q A phi psi epsilon y0
    let a := fun e => splitEndpoint (alpha D P) side (copyA D P marked e) e
    let b := fun e => splitEndpoint (alpha D P) side (copyB D P marked e) e
    (∑ e, (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) *
      (f (a e) - f (b e))^2) ≤
      1 + 21 * ∑ e, (edgeOsc D P marked Q A phi psi epsilon y0 hepsilon e)^2 := by
  intro phi f a b
  let B := fun q => (edgeOsc D P marked Q A phi psi epsilon y0 hepsilon q)^2
  let C := otherIncidentCharge (copyA D P marked) (copyB D P marked) (isRegular D P) B
  have hB (e : Copy D P marked) : 0 ≤ B e := sq_nonneg _
  have hC (x : Vertex D P) (e : Copy D P marked) : 0 ≤ C x e :=
    otherIncidentCharge_nonneg _ _ _ B hB x e
  have endpoint (x : Vertex D P) (e : Copy D P marked)
      (hi : copyA D P marked e = x ∨ copyB D P marked e = x)
      (hx : x ≠ beta D P) (hex : e ≠ exception) :
      ∃ z ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e,
        (f (splitEndpoint (alpha D P) side x e) - angular epsilon y0 z)^2 ≤ C x e := by
    by_cases hxa : x = alpha D P
    · subst x
      have hphi : phi (alpha D P) = 0 := (Repair8.voltage_spec D P hD marked).1
      have hh := hheight e hex hi
      have hsplit : splitEndpoint (alpha D P) side (alpha D P) e = Sum.inr (side e) := by
        simp only [splitEndpoint, dif_pos]
      have hp : phi (alpha D P) ∈
          Set.Icc (min (phi (copyA D P marked e)) (phi (copyB D P marked e)))
            (max (phi (copyA D P marked e)) (phi (copyB D P marked e))) := by
        rcases hi with hi | hi
        · rw [← hi]; exact ⟨min_le_left _ _, le_max_left _ _⟩
        · rw [← hi]; exact ⟨min_le_right _ _, le_max_right _ _⟩
      cases hs : side e
      · refine ⟨(phi (alpha D P), min (psi (A.embedding.leftFace (.inl e)))
            (psi (A.embedding.rightFace (.inl e)))), ⟨hp, le_rfl, min_le_max⟩, ?_⟩
        simp only [hs, Bool.false_eq_true, if_false] at hh
        have hz := angular_axis_eq_zero epsilon y0 _ hepsilon hh
        rw [hsplit, hs]
        change (0 - angular epsilon y0 (phi (alpha D P), _))^2 ≤ _
        rw [hphi, hz, sub_self, zero_pow (by decide : 2 ≠ 0)]
        exact hC _ _
      · refine ⟨(phi (alpha D P), max (psi (A.embedding.leftFace (.inl e)))
            (psi (A.embedding.rightFace (.inl e)))), ⟨hp, min_le_max, le_rfl⟩, ?_⟩
        simp only [hs, if_true] at hh
        have hz := angular_axis_eq_one epsilon y0 _ hepsilon hh
        rw [hsplit, hs]
        change (1 - angular epsilon y0 (phi (alpha D P), _))^2 ≤ _
        rw [hphi, hz, sub_self, zero_pow (by decide : 2 ≠ 0)]
        exact hC _ _
    · cases x with
      | inl k =>
        cases k
        · exact (hxa rfl).elim
        · exact (hx rfl).elim
      | inr x =>
        obtain ⟨z, hz, herr⟩ := minimum_corner_error D P marked hD Q A phi psi
          epsilon y0 hepsilon x e hi
        refine ⟨z, hz, ?_⟩
        simpa only [f, splitEndpoint, dif_neg hxa, splitMinimumTrial, if_neg hx] using herr
  have hterm (e : Copy D P marked) :
      (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) *
        (f (a e) - f (b e))^2 ≤
      (if e = exception then 1 else 0) +
        3 * (B e + C (copyA D P marked e) e + C (copyB D P marked e) e) := by
    have ha := source_voltage_weights D P marked hD (copyA D P marked e)
    have hb := source_voltage_weights D P marked hD (copyB D P marked e)
    have hw : (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) ≤ 1 :=
      (mul_le_mul_of_nonneg_right ha.2 hb.1).trans (by simpa only [one_mul] using hb.2)
    have hweighted : (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) *
        (f (a e) - f (b e))^2 ≤ (f (a e) - f (b e))^2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (sq_nonneg (f (a e) - f (b e)))
    have hn : 0 ≤ 3 * (B e + C (copyA D P marked e) e + C (copyB D P marked e) e) :=
      mul_nonneg (by norm_num) (add_nonneg (add_nonneg (hB e) (hC _ _)) (hC _ _))
    by_cases hex : e = exception
    · rw [if_pos hex]
      have hfa := splitMinimumTrial_range D P marked Q A phi psi epsilon y0 hepsilon (a e)
      have hfb := splitMinimumTrial_range D P marked Q A phi psi epsilon y0 hepsilon (b e)
      have hdiff : (f (a e) - f (b e))^2 ≤ 1 := by nlinarith only [hfa.1, hfa.2, hfb.1, hfb.2]
      linarith only [hweighted, hdiff, hn]
    · rw [if_neg hex, zero_add]
      by_cases hzero : (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) = 0
      · simpa only [hzero, zero_mul] using hn
      have hbeta : phi (beta D P) = 1 := (Repair8.voltage_spec D P hD marked).2.1
      have hax : copyA D P marked e ≠ beta D P := by
        intro hx; apply hzero; rw [hx, hbeta, sub_self, zero_mul]
      have hbx : copyB D P marked e ≠ beta D P := by
        intro hx; apply hzero; rw [hx, hbeta, sub_self, mul_zero]
      obtain ⟨z, hz, herrA⟩ := endpoint _ e (Or.inl rfl) hax hex
      obtain ⟨t, ht, herrB⟩ := endpoint _ e (Or.inr rfl) hbx hex
      have hm := corner_difference_sq_le D P marked Q A phi psi epsilon y0 hepsilon e z t hz ht
      have h3 := sum_three_sq_le (f (a e) - angular epsilon y0 z)
        (angular epsilon y0 z - angular epsilon y0 t) (angular epsilon y0 t - f (b e))
      have heq : (f (a e) - angular epsilon y0 z) +
          (angular epsilon y0 z - angular epsilon y0 t) + (angular epsilon y0 t - f (b e)) =
          f (a e) - f (b e) := by ring
      rw [heq] at h3
      rw [← neg_sub (angular epsilon y0 t), neg_sq] at herrB
      linarith only [hweighted, herrA, herrB, hm, h3]
  have hcharge := source_neighbor_charge_le_six D P marked B hB
  calc
    _ ≤ ∑ e, ((if e = exception then (1 : ℝ) else 0) +
        3 * (B e + C (copyA D P marked e) e + C (copyB D P marked e) e)) :=
      Finset.sum_le_sum (fun e _ => hterm e)
    _ = 1 + 3 * ((∑ e, B e) + ∑ e, (C (copyA D P marked e) e + C (copyB D P marked e) e)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_add_distrib]
      ring
    _ ≤ 1 + 21 * ∑ e, B e := by linarith only [hcharge]

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
