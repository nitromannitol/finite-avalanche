import FiniteAvalanches.Wilson.Lattice.BeurlingGeometry

/-! Connected finite lattice sets cross every smaller integer sup-radius. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.ReciprocalStepThree
open LatticeProb FiniteAvalanches.External.Beurling
open scoped Classical
noncomputable section

private theorem sup_unit_le_one (i : Fin 2) : supNorm (unit i) ≤ 1 := by
  fin_cases i <;>
    simp [supNorm, unit,
      show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]

private theorem adjacent_radius_le (u v : Site 2) (huv : (lattice 2).Adj u v) :
    siteRadius 0 v ≤ siteRadius 0 u + 1 := by
  rw [← supNorm_eq_siteRadius, ← supNorm_eq_siteRadius]
  obtain ⟨i, he | he⟩ := huv
  · rw [he]
    exact (supNorm_triangle _ _).trans (Nat.add_le_add_left (sup_unit_le_one i) _)
  · have hv : v = u + (-unit i) := by rw [he]; abel
    rw [hv]
    have hn : supNorm (-unit i) = supNorm (unit i) := by simp [supNorm]
    exact (supNorm_triangle _ _).trans
      (Nat.add_le_add_left (by rw [hn]; exact sup_unit_le_one i) _)

/-- Pairwise sup distance is bounded by the two origin radii. -/
theorem site_radius_le_origin_sum (x y : Site 2) :
    siteRadius x y ≤ siteRadius 0 x + siteRadius 0 y := by
  have he : siteRadius x y = supNorm (y + -x) := by
    simp only [siteRadius, supNorm, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  have hn : supNorm (-x) = supNorm x := by simp [supNorm]
  rw [he]
  have ht := supNorm_triangle y (-x)
  rw [hn] at ht
  simp only [supNorm_eq_siteRadius] at ht ⊢
  omega

/-- The exact natural-valued finite sup diameter controls the maximal origin radius. -/
theorem diameter_le_twice_origin_radius (K : Finset (Site 2)) :
    K.sup (fun x => K.sup (fun y => siteRadius x y)) ≤
      2 * K.sup (siteRadius 0) := by
  apply Finset.sup_le
  intro x hx
  apply Finset.sup_le
  intro y hy
  exact (site_radius_le_origin_sum x y).trans (by
    have hx' := Finset.le_sup (f := siteRadius 0) hx
    have hy' := Finset.le_sup (f := siteRadius 0) hy
    omega)

private theorem walk_radius_boundary {K : Set (Site 2)} {u v : K}
    (p : ((lattice 2).induce K).Walk u v) (h : ℕ)
    (hu : siteRadius 0 u.val < h) (hv : h ≤ siteRadius 0 v.val) :
    ∃ z ∈ K, siteRadius 0 z = h := by
  induction p with
  | nil => exact False.elim (not_lt_of_ge hv hu)
  | @cons u w v ha p ih =>
    by_cases hw : h ≤ siteRadius 0 w.val
    · refine ⟨w.val, w.property, ?_⟩
      have hs := adjacent_radius_le u.val w.val ha
      omega
    · exact ih (lt_of_not_ge hw) hv

/-- Connectedness and the literal diameter supply the boundary witness internally. -/
theorem connected_boundary_of_diameter (K : Finset (Site 2))
    (hK : ((lattice 2).induce (K : Set (Site 2))).Preconnected)
    (h0 : (0 : Site 2) ∈ K) (h : ℕ) (hpos : 0 < h)
    (hdiam : 2 * h ≤ K.sup (fun x => K.sup (fun y => siteRadius x y))) :
    ∃ z ∈ K, siteRadius 0 z = h := by
  have hb := diameter_le_twice_origin_radius K
  have hm : h ≤ K.sup (siteRadius 0) := by omega
  obtain ⟨z, hz, he⟩ := Finset.sup_mem_of_nonempty
    (f := siteRadius 0) (show K.Nonempty from ⟨0, h0⟩)
  have hzrad : h ≤ siteRadius 0 z := he ▸ hm
  obtain ⟨p⟩ := hK ⟨0, h0⟩ ⟨z, hz⟩
  have hzero : siteRadius 0 (0 : Site 2) = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro i _
    simp only [Pi.zero_apply, sub_self, Int.natAbs_zero, le_refl]
  exact walk_radius_boundary p h (by rw [hzero]; exact hpos) hzrad

/-- The terminal-inclusive localization estimate has its required strict margin at r=2. -/
theorem sixth_power_margin (r : ℕ) (hr : 2 ≤ r) :
    4 * (3 * r + 1) + 4 ≤ r ^ 6 - 1 := by
  have hp : 32 ≤ r ^ 5 := by
    simpa using pow_le_pow_left₀ (Nat.zero_le 2) hr 5
  have hh : 32 * r ≤ r ^ 6 := by
    simpa only [pow_succ] using Nat.mul_le_mul_right r hp
  omega

end
end FiniteAvalanches.Wilson.Lattice.ReciprocalStepThree
