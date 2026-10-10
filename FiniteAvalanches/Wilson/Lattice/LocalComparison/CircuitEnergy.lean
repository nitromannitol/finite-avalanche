import FiniteAvalanches.Wilson.Lattice.LocalComparison.SquareGeometry

set_option autoImplicit false
namespace LocalCircuitEnergy
open LatticeProb FiniteAvalanches
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.Plane.SourceLattice
open LocalSquareGeometry
open scoped Classical BigOperators
noncomputable section

private theorem four_div_sum_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    4/(a+b) ≤ 1/a+1/b := by
  rw [div_add_div _ _ ha.ne' hb.ne']
  apply (div_le_div_iff₀ (add_pos ha hb) (mul_pos ha hb)).mpr
  nlinarith only [sq_nonneg (a-b)]

/-- Telescoping and Cauchy--Schwarz on each of the two complementary arcs. -/
private theorem cyclic_energy (g : ℕ → ℝ) (n a b : ℕ)
    (hab : a < b) (hbn : b < n) (hcycle : g n = g 0)
    (hdiff : (g b-g a)^2 = 1) :
    4/(n : ℝ) ≤ ∑ i ∈ Finset.range n, (g (i+1)-g i)^2 := by
  let S := Finset.Ico a b
  let T := Finset.range n \ S
  let d := fun i => g (i+1)-g i
  have hS : S ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hi).2.trans hbn)
  have hsumS : (∑ i ∈ S, d i) = g b-g a := by
    rw [Finset.sum_Ico_eq_sub _ hab.le,Finset.sum_range_sub,Finset.sum_range_sub]
    ring
  have hsumAll : (∑ i ∈ Finset.range n, d i) = 0 := by
    rw [Finset.sum_range_sub,hcycle,sub_self]
  have hsumT : (∑ i ∈ T, d i) = -(g b-g a) := by
    rw [Finset.sum_sdiff_eq_sub hS,hsumAll,hsumS,zero_sub]
  have hcardS : S.card = b-a := Nat.card_Ico a b
  have hcardT : T.card = n-(b-a) := by
    rw [Finset.card_sdiff_of_subset hS,Finset.card_range,hcardS]
  have hposS : 0 < (S.card : ℝ) := by
    rw [hcardS]
    exact_mod_cast Nat.sub_pos_of_lt hab
  have hposT : 0 < (T.card : ℝ) := by
    rw [hcardT]
    exact_mod_cast Nat.sub_pos_of_lt ((Nat.sub_le b a).trans_lt hbn)
  have hcsS := Finset.sum_mul_sq_le_sq_mul_sq S d (fun _ => (1 : ℝ))
  have hcsT := Finset.sum_mul_sq_le_sq_mul_sq T d (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcsS hcsT
  rw [hsumS,hdiff] at hcsS
  rw [hsumT,neg_sq,hdiff] at hcsT
  have hleS : 1/(S.card : ℝ) ≤ ∑ i ∈ S, d i^2 :=
    (div_le_iff₀ hposS).mpr hcsS
  have hleT : 1/(T.card : ℝ) ≤ ∑ i ∈ T, d i^2 :=
    (div_le_iff₀ hposT).mpr hcsT
  have hc : (S.card : ℝ)+(T.card : ℝ) = n := by
    rw [← Nat.cast_add,hcardS,hcardT]
    congr 1
    omega
  have hsumE := Finset.sum_sdiff (f := fun i => d i^2) hS
  calc
    4/(n : ℝ) = 4/((S.card : ℝ)+(T.card : ℝ)) := by rw [hc]
    _ ≤ 1/(S.card : ℝ)+1/(T.card : ℝ) := four_div_sum_le _ _ hposS hposT
    _ ≤ (∑ i ∈ S, d i^2)+(∑ i ∈ T, d i^2) := add_le_add hleS hleT
    _ = ∑ i ∈ Finset.range n, d i^2 := by rw [add_comm,hsumE]

/-- The two-arc bound for the explicit original-copy square, for every potential. -/
theorem square_energy_lower (j : ℕ) (hj : 0 < j) (f : Site 2 → ℝ)
    (hzero : ∃ x, siteRadius 0 x = j ∧ f x = 0)
    (hone : ∃ x, siteRadius 0 x = j ∧ f x = 1) :
    1/(2*(j : ℝ)) ≤ ∑ e ∈ copies j, (f (originalA e)-f (originalB e))^2 := by
  obtain ⟨x0,hx0,hf0⟩ := hzero
  obtain ⟨x1,hx1,hf1⟩ := hone
  obtain ⟨a,ha⟩ := vertex_surjective j hj x0 hx0
  obtain ⟨b,hb⟩ := vertex_surjective j hj x1 hx1
  let g := fun t => f (vertex j t)
  have hcycle : g (8*j) = g 0 := congrArg f (vertex_end j)
  have hg0 : g a.val = 0 := by dsimp [g]; rw [ha,hf0]
  have hg1 : g b.val = 1 := by dsimp [g]; rw [hb,hf1]
  have hne : a.val ≠ b.val := by
    intro he
    rw [he,hg1] at hg0
    norm_num at hg0
  have hbound : 4/(8*j : ℕ) ≤ ∑ t ∈ Finset.range (8*j), (g (t+1)-g t)^2 := by
    rcases lt_or_gt_of_ne hne with hab | hba
    · exact cyclic_energy g (8*j) a.val b.val hab b.isLt hcycle (by rw [hg1,hg0]; norm_num)
    · exact cyclic_energy g (8*j) b.val a.val hba a.isLt hcycle (by rw [hg0,hg1]; norm_num)
  have he (t : Fin (8*j)) :
      (f (originalA (edge j t.val))-f (originalB (edge j t.val)))^2 =
        (g (t.val+1)-g t.val)^2 := by
    rcases edge_endpoints j t.val t.isLt with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [ha,hb]
      dsimp [g]; ring
    · rw [ha,hb]
  rw [copies,Finset.sum_image (edge_injective j hj).injOn]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun t => (g (t+1)-g t)^2) (8*j)]
  have hid : 1/(2*(j : ℝ)) = 4/(8*j : ℕ) := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [hid]
  exact hbound

end
end LocalCircuitEnergy
