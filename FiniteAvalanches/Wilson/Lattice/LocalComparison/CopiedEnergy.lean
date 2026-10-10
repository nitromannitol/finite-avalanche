import FiniteAvalanches.Wilson.Lattice.LocalComparison.CircuitEnergy

set_option autoImplicit false
namespace LocalCopiedEnergy
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.Plane.SourceLattice
open LocalSquareGeometry
open scoped Classical BigOperators
noncomputable section

theorem unretained_zero (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (phi : Vertex D P → ℝ) (e : OriginalCopy)
    (he : e ∉ retainedCopies D P marked) (hne : e ≠ marked.val) :
    (phi (project D P (originalA e))-phi (project D P (originalB e)))^2 = 0 := by
  by_cases hd : originalA e ∈ D ∨ originalB e ∈ D
  · have hproj : project D P (originalA e) = project D P (originalB e) := by
      by_contra h
      exact he ((mem_retainedCopies D P marked e).mpr ⟨hd,h,hne⟩)
    rw [hproj,sub_self]
    norm_num
  · have ha : originalA e ∉ D := fun ha => hd (Or.inl ha)
    have hb : originalB e ∉ D := fun hb => hd (Or.inr hb)
    rw [(project_eq_alpha_iff D P _).mpr ha,(project_eq_alpha_iff D P _).mpr hb,sub_self]
    norm_num

/-- Sum comparison on original physical IDs, including all parallel copies. -/
theorem original_sum_le_energy (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (phi : Vertex D P → ℝ) (S : Finset OriginalCopy) (hmark : marked.val ∉ S) :
    (∑ e ∈ S, (phi (project D P (originalA e))-phi (project D P (originalB e)))^2) ≤
      energy (copyA D P marked) (copyB D P marked) phi := by
  let E := fun e => (phi (project D P (originalA e))-phi (project D P (originalB e)))^2
  let T := retainedCopies D P marked
  have hsum : (∑ e ∈ T, E e) = energy (copyA D P marked) (copyB D P marked) phi := by
    exact (Finset.sum_coe_sort T E).symm
  have heq : (∑ e ∈ T, E e) = ∑ e ∈ S ∪ T, E e := by
    apply Finset.sum_subset Finset.subset_union_right
    intro e he heT
    have heS : e ∈ S := (Finset.mem_union.mp he).resolve_right heT
    exact unretained_zero D P marked phi e heT (fun he => hmark (he ▸ heS))
  calc
    (∑ e ∈ S, E e) ≤ ∑ e ∈ S ∪ T, E e :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun e _ _ => sq_nonneg _)
    _ = ∑ e ∈ T, E e := heq.symm
    _ = energy (copyA D P marked) (copyB D P marked) phi := hsum

theorem circuits_sum_le_energy (r : ℕ) (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (b : Site 2)
    (hm : (originalA marked.val = 0 ∧ originalB marked.val = b) ∨
      (originalA marked.val = b ∧ originalB marked.val = 0)) (phi : Vertex D P → ℝ) :
    (∑ j ∈ Finset.Icc 1 r, ∑ e ∈ copies j,
      (phi (project D P (originalA e))-phi (project D P (originalB e)))^2) ≤
        energy (copyA D P marked) (copyB D P marked) phi := by
  let S := (Finset.Icc 1 r).biUnion copies
  have hmark : marked.val ∉ S := by
    intro he
    obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp he
    exact source_mark_not_mem j (by have := (Finset.mem_Icc.mp hj).1; omega) D P marked b hm he
  have hdis : (↑(Finset.Icc 1 r) : Set ℕ).PairwiseDisjoint copies :=
    fun j _ k _ hjk => copies_disjoint j k hjk
  have hl := original_sum_le_energy D P marked phi S hmark
  rw [Finset.sum_biUnion hdis] at hl
  exact hl

/-- Both source root sets supply an actual zero/one vertex on every square. -/
theorem roots_meet_circuits (r : ℕ) (R : RootPair)
    (h0 : (0 : Site 2) ∈ R.zero) (hZero : ((lattice 2).induce R.zero).Connected)
    (hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x)
    (b y : Site 2) (hadj : (lattice 2).Adj 0 b) (q : (lattice 2).Walk b y)
    (hy : siteRadius 0 y = r) (D : Finset (Site 2)) (P : OneSet D)
    (hZD : R.zero ⊆ (D : Set (Site 2))ᶜ) (hPQ : P.val.image Subtype.val = q.support.toFinset)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 r) :
    (∃ x, siteRadius 0 x = j ∧ project D P x = alpha D P) ∧
    (∃ x, siteRadius 0 x = j ∧ project D P x = beta D P) := by
  obtain ⟨z,hz,hzr⟩ := hfar
  obtain ⟨p⟩ := hZero.preconnected ⟨0,h0⟩ ⟨z,hz⟩
  let f := (SimpleGraph.Embedding.induce R.zero (G := lattice 2)).toHom
  let p0 : (lattice 2).Walk (0 : Site 2) z := p.map f
  obtain ⟨x,hx,hxj⟩ := JointMetricGeometry.walk_meets_radius 0 j p0
    (by simp [siteRadius]) (by have := (Finset.mem_Icc.mp hj).2; omega)
  have hxZ : x ∈ R.zero := by
    change x ∈ (p.map f).support at hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨u,_,hu⟩ := List.mem_map.mp hx
    exact hu ▸ u.property
  obtain ⟨w,hw,hwj⟩ := JointMetricGeometry.walk_meets_radius 0 j q
    ((JointMetricGeometry.radius_adj_le_one 0 b hadj).trans (Finset.mem_Icc.mp hj).1)
    (by rw [hy]; exact (Finset.mem_Icc.mp hj).2)
  refine ⟨⟨x,hxj,(project_eq_alpha_iff D P x).mpr (hZD hxZ)⟩,
    ⟨w,hwj,(project_eq_beta_iff D P w).mpr ?_⟩⟩
  rw [hPQ]
  exact List.mem_toFinset.mpr hw

/-- Every admissible potential on the actual network pays every original square. -/
theorem admissible_energy_lower (r : ℕ) (R : RootPair)
    (h0 : (0 : Site 2) ∈ R.zero) (hZero : ((lattice 2).induce R.zero).Connected)
    (hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x)
    (b y : Site 2) (hadj : (lattice 2).Adj 0 b) (q : (lattice 2).Walk b y)
    (hy : siteRadius 0 y = r) (D : Finset (Site 2)) (P : OneSet D)
    (hZD : R.zero ⊆ (D : Set (Site 2))ᶜ) (hPQ : P.val.image Subtype.val = q.support.toFinset)
    (marked : MarkedCopy D P)
    (hm : (originalA marked.val = 0 ∧ originalB marked.val = b) ∨
      (originalA marked.val = b ∧ originalB marked.val = 0))
    (phi : Vertex D P → ℝ) (hp0 : phi (alpha D P) = 0) (hp1 : phi (beta D P) = 1) :
    (∑ j ∈ Finset.Icc 1 r, 1/(2*(j : ℝ))) ≤
      energy (copyA D P marked) (copyB D P marked) phi := by
  apply le_trans _ (circuits_sum_le_energy r D P marked b hm phi)
  apply Finset.sum_le_sum
  intro j hj
  obtain ⟨⟨x,hx,hx0⟩,⟨w,hw,hw1⟩⟩ := roots_meet_circuits r R h0 hZero hfar b y hadj q hy D P hZD hPQ j hj
  exact LocalCircuitEnergy.square_energy_lower j (by have := (Finset.mem_Icc.mp hj).1; omega)
    (fun z => phi (project D P z)) ⟨x,hx,hx0 ▸ hp0⟩ ⟨w,hw,hw1 ▸ hp1⟩

end
end LocalCopiedEnergy
