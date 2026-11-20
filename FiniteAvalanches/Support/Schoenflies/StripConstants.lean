/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/StripConstants.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Strip
import FiniteAvalanches.Support.Schoenflies.PolyPath

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




















































open Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i j : ZMod (m + 3)} {c lam : ℝ}

 

theorem isCompact_edge : IsCompact (P.edge i) := isCompact_segment _ _

theorem isCompact_carrier (P : ClosedPolygon m) : IsCompact P.carrier :=
  isCompact_iUnion fun _ => isCompact_edge

theorem continuous_pt (P : ClosedPolygon m) (i : ZMod (m + 3)) : Continuous (P.pt i) := by
  have h : P.pt i = fun c : ℝ => P.vertex i + c • P.tang i := funext fun _ => pt_eq
  rw [h]
  exact continuous_const.add (continuous_id.smul continuous_const)

 




 


theorem vertex_notMem_edge (hj1 : j ≠ i - 1) (hj2 : j ≠ i) : P.vertex i ∉ P.edge j := by
  intro hx
  
  have hmem : P.vertex i ∈ P.edge j ∩ P.edge i := ⟨hx, vertex_mem_edge⟩
  have hsub := P.edges_meet j i hj2 hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · exact hj2 (P.vertex_inj h).symm
  · exact hj1 (by rw [P.vertex_inj h]; ring)

 

def trimmed (P : ClosedPolygon m) (i : ZMod (m + 3)) (lam : ℝ) : Set Plane :=
  P.pt i '' Set.Icc lam (P.len i - lam)

theorem pt_mem_trimmed (hc : c ∈ Set.Icc lam (P.len i - lam)) : P.pt i c ∈ P.trimmed i lam :=
  ⟨c, hc, rfl⟩

theorem isCompact_trimmed : IsCompact (P.trimmed i lam) :=
  isCompact_Icc.image (P.continuous_pt i)

 



theorem trimmed_disjoint_edge (hlam : 0 < lam) (hij : j ≠ i) :
    Disjoint (P.trimmed i lam) (P.edge j) := by
  rw [Set.disjoint_left]
  rintro x ⟨c, hc, rfl⟩ hx
  have hc0 : (0 : ℝ) ≤ c := le_trans hlam.le hc.1
  have hcl : c ≤ P.len i := le_trans hc.2 (by linarith)
  have hmem : P.pt i c ∈ P.edge i ∩ P.edge j := ⟨pt_mem_edge ⟨hc0, hcl⟩, hx⟩
  have hsub := P.edges_meet i j (Ne.symm hij) hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · 
    have h0 : |c| = 0 := by rw [← dist_pt_vertex (P := P) (i := i) (c := c), h, dist_self]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.1]
  · 
    have h0 : |c| = P.len i := by
      rw [← dist_pt_vertex (P := P) (i := i) (c := c), h, len, dist_eq_norm]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.2]

end ClosedPolygon

 






namespace StripData

variable {P : ClosedPolygon m} (D : StripData P)

 
theorem nbhd_subset_thickening : D.nbhd ⊆ thickening D.R P.carrier := by
  intro x hx
  have hx' : x ∈ D.sideL ∪ D.sideR ∪ P.carrier := hx
  rcases hx' with (hL | hR) | hc
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hL
    rcases hi with hi | hi
    · exact mem_thickening_iff.2 ⟨P.vertex i, ClosedPolygon.vertex_mem_carrier, hi.2⟩
    · obtain ⟨c, hcmem, hd⟩ := D.exists_foot (Or.inl hi)
      exact mem_thickening_iff.2 ⟨P.pt i c,
        ClosedPolygon.edge_subset_carrier (D.pt_mem_edge_of_trim hcmem), lt_trans hd D.rho_lt_R⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hR
    rcases hi with hi | hi
    · exact mem_thickening_iff.2 ⟨P.vertex i, ClosedPolygon.vertex_mem_carrier, hi.2⟩
    · obtain ⟨c, hcmem, hd⟩ := D.exists_foot (Or.inr hi)
      exact mem_thickening_iff.2 ⟨P.pt i c,
        ClosedPolygon.edge_subset_carrier (D.pt_mem_edge_of_trim hcmem), lt_trans hd D.rho_lt_R⟩
  · exact self_subset_thickening D.R_pos _ hc

end StripData

 

namespace ClosedPolygon

 



theorem exists_cone_radius (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) :
    ∃ R > 0, (∀ i, R ≤ P.len i) ∧
      (∀ i j, i ≠ j → 2 * R ≤ dist (P.vertex i) (P.vertex j)) ∧
      (∀ i j, j ≠ i - 1 → j ≠ i → ∀ y ∈ P.edge j, 2 * R ≤ dist (P.vertex i) y) ∧
      thickening R P.carrier ⊆ U := by
  
  obtain ⟨e₁, he₁, hlen⟩ :=
    exists_pos_le_of_finite (Set.finite_univ (α := ZMod (m + 3))) (f := fun i => P.len i)
      (fun _ _ => len_pos)
  
  have h₂ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.1 ≠ p.2 → ε ≤ dist (P.vertex p.1) (P.vertex p.2)) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h hne
      exact le_trans hδε (h hne)
    · rintro ⟨i, j⟩ -
      by_cases hij : i = j
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · exact ⟨dist (P.vertex i) (P.vertex j),
          dist_pos.2 fun h => hij (P.vertex_inj h), fun _ => le_refl _⟩
  
  have h₃ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.2 ≠ p.1 - 1 → p.2 ≠ p.1 → ∀ y ∈ P.edge p.2, ε ≤ dist (P.vertex p.1) y) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h h1 h2 y hy
      exact le_trans hδε (h h1 h2 y hy)
    · rintro ⟨i, j⟩ -
      by_cases hj1 : j = i - 1
      · exact ⟨1, one_pos, fun h => absurd hj1 h⟩
      by_cases hj2 : j = i
      · exact ⟨1, one_pos, fun _ h => absurd hj2 h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_singleton isCompact_edge
          (Set.disjoint_singleton_left.2 (vertex_notMem_edge hj1 hj2))
        exact ⟨ρ, hρ, fun _ _ y hy => hsep _ rfl y hy⟩
  
  obtain ⟨e₄, he₄, hthick⟩ := Plane.exists_thickening_subset (isCompact_carrier P) hU hPU
  obtain ⟨e₂, he₂, hvv⟩ := h₂
  obtain ⟨e₃, he₃, hve⟩ := h₃
  refine ⟨min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄),
    lt_min (lt_min he₁ (by linarith)) (lt_min (by linarith) he₄), fun i => ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (hlen i (Set.mem_univ i))
  · intro i j hij
    have h := hvv (i, j) (Set.mem_univ _) hij
    have : min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄) ≤ e₂ / 2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  · intro i j hj1 hj2 y hy
    have h := hve (i, j) (Set.mem_univ _) hj1 hj2 y hy
    have : min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄) ≤ e₃ / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · exact subset_trans
      (thickening_mono (le_trans (min_le_right _ _) (min_le_right _ _)) _) hthick

 

theorem exists_germ_bound (P : ClosedPolygon m) (i : ZMod (m + 3)) {lam : ℝ} (hlam : 0 < lam) :
    ∃ ε > 0, ε * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤
      lam * |det (P.rayIn i) (P.tang i)| := by
  have hb : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 det_rays_ne_zero
  have ha : 0 < 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
    have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
  refine ⟨lam * |det (P.rayIn i) (P.tang i)| / (1 + |inner ℝ (P.rayIn i) (P.tang i)|),
    div_pos (mul_pos hlam hb) ha, le_of_eq ?_⟩
  field_simp

 



theorem exists_half_width (P : ClosedPolygon m) {lam : ℝ} (hlam : 0 < lam) :
    ∃ rho > 0, rho < lam ∧
      (∀ i j, j ≠ i → ∀ c ∈ Set.Icc lam (P.len i - lam), ∀ y ∈ P.edge j,
        2 * rho ≤ dist (P.pt i c) y) ∧
      (∀ i, rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤
        lam * |det (P.rayIn i) (P.tang i)|) := by
  
  have h₁ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.2 ≠ p.1 → ∀ x ∈ P.trimmed p.1 lam, ∀ y ∈ P.edge p.2, ε ≤ dist x y) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h hne x hx y hy
      exact le_trans hδε (h hne x hx y hy)
    · rintro ⟨i, j⟩ -
      by_cases hij : j = i
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_trimmed isCompact_edge
          (trimmed_disjoint_edge hlam hij)
        exact ⟨ρ, hρ, fun _ => hsep⟩
  
  have h₂ : ∃ ε > 0, ∀ i : ZMod (m + 3), i ∈ (Set.univ : Set _) →
      ε * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤ lam * |det (P.rayIn i) (P.tang i)| := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro i δ ε _ hδε h
      have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
        have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
      nlinarith
    · intro i _
      exact P.exists_germ_bound i hlam
  obtain ⟨ε₁, hε₁, htrim⟩ := h₁
  obtain ⟨ε₂, hε₂, hgerm⟩ := h₂
  refine ⟨min (min (ε₁ / 2) ε₂) (lam / 2),
    lt_min (lt_min (by linarith) hε₂) (by linarith), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro i j hij c hc y hy
    have h := htrim (i, j) (Set.mem_univ _) hij _ (pt_mem_trimmed hc) y hy
    have hm : min (min (ε₁ / 2) ε₂) (lam / 2) ≤ ε₁ / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  · intro i
    have h := hgerm i (Set.mem_univ _)
    have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
      have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
    have hm : min (min (ε₁ / 2) ε₂) (lam / 2) ≤ ε₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith

end ClosedPolygon

open ClosedPolygon

 


theorem exists_stripData_subset (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) : ∃ D : StripData P, D.nbhd ⊆ U := by
  obtain ⟨R, hR, hRlen, hRvv, hRve, hRU⟩ := P.exists_cone_radius hU hPU
  have hlam : (0 : ℝ) < R / 5 := by linarith
  have hlen4 : ∀ i, 4 * (R / 5) < P.len i := fun i => by have := hRlen i; linarith
  obtain ⟨rho, hrho, hrl, htrim, hgerm⟩ := P.exists_half_width hlam
  refine ⟨⟨R, R / 5, rho, hrho, hrl, by linarith, hlen4, hRlen, hRvv, hRve, htrim, hgerm⟩, ?_⟩
  exact subset_trans (StripData.nbhd_subset_thickening _) hRU

 
theorem exists_stripData (P : ClosedPolygon m) : Nonempty (StripData P) :=
  ⟨(exists_stripData_subset P isOpen_univ (subset_univ _)).choose⟩

end Schoenflies
