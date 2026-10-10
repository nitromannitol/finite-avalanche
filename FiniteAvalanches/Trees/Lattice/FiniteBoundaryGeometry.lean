import FiniteAvalanches.Trees.Lattice.EuclideanPaths
import FiniteAvalanches.Trees.Lattice.Dual

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.BarlowMasson
open LatticeProb FiniteAvalanches.Trees.Lattice
open scoped Classical
noncomputable section

/-- Each coordinate displacement is bounded by the literal Euclidean distance. -/
theorem coordinate_abs_le_euclideanDistance (x z : Site 2) (i : Fin 2) :
    |((z i - x i : ℤ) : ℝ)| ≤ euclideanDistance x z := by
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (((z j - x j : ℤ) : ℝ)))
    (Finset.mem_univ i)

/-- An extremal vertex of a finite set gives a genuine crossing edge, with both
face-lattice dual endpoints at least as far in its extremal coordinate. -/
theorem finite_set_far_boundary (A : Set (Site 2)) (hA : A.Finite)
    (v z : Site 2) (hz : z ∈ A) (i : Fin 2) (m : ℤ)
    (hfar : m < |z i - v i|) :
    ∃ p : Site 2 × Fin 2, p.2 = i ∧
      ((p.1 ∈ A ∧ p.1 + unit p.2 ∉ A) ∨
        (p.1 ∉ A ∧ p.1 + unit p.2 ∈ A)) ∧
      m < |(dualBaseInv p).1 i - v i| ∧
      m < |((dualBaseInv p).1 + unit (dualBaseInv p).2) i - v i| := by
  obtain ⟨a, ha, hmax⟩ := hA.toFinset.exists_max_image
    (fun a => |a i - v i|) ⟨z, hA.mem_toFinset.mpr hz⟩
  have haA : a ∈ A := hA.mem_toFinset.mp ha
  have ham : m < |a i - v i| := lt_of_lt_of_le hfar
    (hmax z (hA.mem_toFinset.mpr hz))
  have horth : (1 : Fin 2) - i ≠ i := by fin_cases i <;> decide
  by_cases hpos : 0 ≤ a i - v i
  · have hout : a + unit i ∉ A := by
      intro hin
      have h := hmax (a + unit i) (hA.mem_toFinset.mpr hin)
      simp only [Pi.add_apply, unit, Pi.single_eq_same] at h
      rw [abs_of_nonneg hpos, abs_of_nonneg (by omega)] at h
      omega
    refine ⟨(a, i), rfl, Or.inl ⟨haA, hout⟩, ?_, ?_⟩
    · simpa [dualBaseInv, unit, Ne.symm horth] using ham
    · simpa [dualBaseInv, unit, Ne.symm horth] using ham
  · have hneg : a i - v i < 0 := lt_of_not_ge hpos
    have hout : a - unit i ∉ A := by
      intro hin
      have h := hmax (a - unit i) (hA.mem_toFinset.mpr hin)
      simp only [Pi.sub_apply, unit, Pi.single_eq_same] at h
      rw [abs_of_neg hneg, abs_of_neg (by omega)] at h
      omega
    have hamp : m < |(a - unit i) i - v i| := by
      simp only [Pi.sub_apply, unit, Pi.single_eq_same]
      rw [abs_of_neg (by omega)]
      rw [abs_of_neg hneg] at ham
      omega
    refine ⟨(a - unit i, i), rfl, Or.inr ⟨hout, ?_⟩, ?_, ?_⟩
    · simpa only [sub_add_cancel] using haA
    · simpa [dualBaseInv, unit, Ne.symm horth] using hamp
    · simpa [dualBaseInv, unit, Ne.symm horth] using hamp

/-- The two endpoints of a boundary dual edge reach beyond `m-1` from every
face-lattice center within one coordinate unit of the original source. -/
theorem finite_set_far_dual_endpoints (A : Set (Site 2)) (hA : A.Finite)
    (v z : Site 2) (hz : z ∈ A) (i : Fin 2) (m : ℤ)
    (hfar : m < |z i - v i|) :
    ∃ p : Site 2 × Fin 2,
      ((p.1 ∈ A ∧ p.1 + unit p.2 ∉ A) ∨
        (p.1 ∉ A ∧ p.1 + unit p.2 ∈ A)) ∧
      ∀ x : Site 2, (∀ j : Fin 2, |x j - v j| ≤ 1) →
        ∀ w ∈ ({(dualBaseInv p).1,
          (dualBaseInv p).1 + unit (dualBaseInv p).2} : Set (Site 2)),
          (m : ℝ) - 1 < euclideanDistance x w := by
  obtain ⟨p, _, hcross, hleft, hright⟩ :=
    finite_set_far_boundary A hA v z hz i m hfar
  refine ⟨p, hcross, ?_⟩
  intro x hx w hw
  have hwfar : m < |w i - v i| := by
    rcases Set.mem_insert_iff.mp hw with h | h
    · simpa only [h] using hleft
    · have he := Set.mem_singleton_iff.mp h
      simpa only [he] using hright
  have htri : |w i - v i| ≤ |w i - x i| + |x i - v i| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (w i - x i) (x i - v i)
  have hcoord : m - 1 < |w i - x i| := by
    have := hx i
    omega
  have hreal : (m : ℝ) - 1 < |((w i - x i : ℤ) : ℝ)| := by
    exact_mod_cast hcoord
  exact lt_of_lt_of_le hreal (coordinate_abs_le_euclideanDistance x w i)

end
end FiniteAvalanches.Trees.Lattice.BarlowMasson
