import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.Exterior
import FiniteAvalanches.Needle.Geometry

set_option autoImplicit false
namespace JointMetricGeometry
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

theorem radius_triangle (a b c : Site 2) : siteRadius a c ≤ siteRadius a b + siteRadius b c := by
  apply (siteRadius_le_iff _ _ _).mpr
  intro i
  have hab := (siteRadius_le_iff a b (siteRadius a b)).mp le_rfl i
  have hbc := (siteRadius_le_iff b c (siteRadius b c)).mp le_rfl i
  have he : c i-a i = (b i-a i)+(c i-b i) := by ring
  rw [he, Nat.cast_add]
  exact (abs_add_le _ _).trans (add_le_add hab hbc)

theorem radius_symm (a b : Site 2) : siteRadius a b = siteRadius b a := by
  apply le_antisymm
  · apply (siteRadius_le_iff _ _ _).mpr
    intro i
    rw [abs_sub_comm]
    exact (siteRadius_le_iff _ _ _).mp le_rfl i
  · apply (siteRadius_le_iff _ _ _).mpr
    intro i
    rw [abs_sub_comm]
    exact (siteRadius_le_iff _ _ _).mp le_rfl i

theorem radius_adj_le_one (a b : Site 2) (h : (lattice 2).Adj a b) : siteRadius a b ≤ 1 := by
  apply (siteRadius_le_iff _ _ _).mpr
  obtain ⟨j,hj | hj⟩ := Graph.Zd.adj_iff.mp h
  · rw [hj]
    intro i
    by_cases hi : i = j
    · subst i; simp [unit]
    · simp [unit,hi]
  · rw [hj]
    intro i
    by_cases hi : i = j
    · subst i; simp [unit]
    · simp [unit,hi]

theorem radius_cast (x : Site 2) : (siteRadius 0 x : ℤ) = Needle.radius x := by
  apply le_antisymm
  · have hb : siteRadius 0 x ≤ (Needle.radius x).toNat := by
      apply (siteRadius_le_iff _ _ _).mpr
      intro i
      rw [Pi.zero_apply,sub_zero,Int.toNat_of_nonneg (Needle.radius_nonneg x)]
      exact (Needle.radius_le_iff x (Needle.radius x)).mp le_rfl i
    have := Nat.cast_le (α := ℤ).mpr hb
    simpa only [Int.toNat_of_nonneg (Needle.radius_nonneg x)] using this
  · apply (Needle.radius_le_iff _ _).mpr
    intro i
    simpa only [Pi.zero_apply,sub_zero] using
      (siteRadius_le_iff 0 x (siteRadius 0 x)).mp le_rfl i

theorem walk_meets_radius (w : Site 2) (r : ℕ) {a b : Site 2}
    (p : (lattice 2).Walk a b) (ha : siteRadius w a ≤ r) (hb : r ≤ siteRadius w b) :
    ∃ y ∈ p.support, siteRadius w y = r := by
  induction p with
  | nil => exact ⟨_,by simp,Nat.le_antisymm ha hb⟩
  | @cons a c b e p ih =>
    by_cases hc : siteRadius w c ≤ r
    · obtain ⟨y,hy,he⟩ := ih hc hb
      exact ⟨y,List.mem_cons_of_mem a hy,he⟩
    · have ht := radius_triangle w a c
      have hstep := radius_adj_le_one a c e
      exact ⟨a,by simp,by omega⟩

/-- A cofinite connected root set containing a neighbor meets every larger sphere. -/
theorem connected_cofinite_meets_radius (S : Set (Site 2))
    (hc : ((lattice 2).induce S).Connected) (hf : Sᶜ.Finite)
    (w : Site 2) (r : ℕ) (hr : 1 ≤ r) (hn : ∃ z ∈ S, (lattice 2).Adj w z) :
    ∃ y ∈ S, siteRadius w y = r := by
  obtain ⟨z,hz,hadj⟩ := hn
  obtain ⟨b,hb⟩ := (hf.union (window w r).finite_toSet).exists_notMem
  have hbS : b ∈ S := by
    by_contra h; exact hb (Or.inl h)
  have hbfar : r ≤ siteRadius w b := by
    have hnB : b ∉ window w r := fun h => hb (Or.inr h)
    have := (mem_window w b r).not.mp hnB
    omega
  obtain ⟨p⟩ := hc.preconnected ⟨z,hz⟩ ⟨b,hbS⟩
  let f := (SimpleGraph.Embedding.induce S (G := lattice 2)).toHom
  obtain ⟨y,hy,he⟩ := walk_meets_radius w r (p.map f)
    ((radius_adj_le_one w z hadj).trans hr) hbfar
  refine ⟨y,?_,he⟩
  rw [SimpleGraph.Walk.support_map] at hy
  obtain ⟨x,_,hx⟩ := List.mem_map.mp hy
  exact hx ▸ x.property

theorem large_extent (K : Finset (Site 2))
    (r : ℕ) (hr : 0 < r) (hd : 16*r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)))
    (w : Site 2) : ∃ x ∈ K, 2*r ≤ siteRadius w x := by
  by_contra hn
  push Not at hn
  have hbound : K.sup (fun x => K.sup (fun y => siteRadius x y)) ≤ 4*r-2 := by
    apply Finset.sup_le
    intro x hx
    apply Finset.sup_le
    intro y hy
    have hxw := hn x hx
    have hyw := hn y hy
    have ht := radius_triangle x w y
    rw [radius_symm x w] at ht
    omega
  omega

theorem translated_window_subset (w : Site 2) (r : ℕ) (hw : siteRadius 0 w ≤ r) :
    window w (2*r) ⊆ boxSites (3*r) := by
  intro x hx
  have hxt := radius_triangle 0 w x
  have hxr := (mem_window w x (2*r)).mp hx
  apply (mem_box_sites (3*r) x).mpr
  have hcoords := (siteRadius_le_iff 0 x (3*r)).mp (by omega : siteRadius 0 x ≤ 3*r)
  intro i
  simpa only [Pi.zero_apply,sub_zero,abs_le] using hcoords i

end
end JointMetricGeometry
