/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/PolygonalJordan.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.PolygonBridge
import FiniteAvalanches.Support.Schoenflies.StripLocal
import FiniteAvalanches.Support.Schoenflies.CrosscutCells
import FiniteAvalanches.Support.Schoenflies.Bounded

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




















































open Bornology Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

 




 
private theorem isBounded_closedSquare (r : ℝ) : IsBounded (Plane.closedSquare 0 r) := by
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := Real.sqrt 2 * r)).subset ?_
  intro x hx
  have hsup : Plane.supNorm x ≤ r := by simpa [Plane.closedSquare] using hx
  have : ‖x‖ ≤ Real.sqrt 2 * r :=
    le_trans (Plane.norm_le_sqrt_two_mul_supNorm x)
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

 
private theorem not_isBounded_beyondSquare (r : ℝ) : ¬ IsBounded (Plane.beyondSquare r) := by
  intro hb
  obtain ⟨s, -, hs⟩ := Plane.exists_closedSquare_of_isBounded hb
  set t : ℝ := max (max r s) 0 + 1 with ht
  have ht0 : 0 ≤ t := by have := le_max_right (max r s) 0; simp only [ht]; linarith
  have htr : r < t := by
    have h1 := le_max_left r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  have hts : s < t := by
    have h1 := le_max_right r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  have hmem : Plane.mk t 0 ∈ Plane.beyondSquare r :=
    Or.inl (show r < |t| by rw [abs_of_nonneg ht0]; exact htr)
  have hin : Plane.supDist (Plane.mk t 0) 0 ≤ s := hs hmem
  rw [Plane.supDist_zero] at hin
  have h1 : |t| ≤ Plane.supNorm (Plane.mk t 0) := by
    simp only [Plane.supNorm]; exact le_max_left _ _
  rw [abs_of_nonneg ht0] at h1
  linarith

 



private theorem exists_beyond_of_fwd_lt {u : Plane} (hu : Plane.IsDirection u) (r M : ℝ) :
    ∃ q : Plane, q ∈ Plane.beyondSquare r ∧ M < fwd u q := by
  have hnorm : u 0 ^ 2 + u 1 ^ 2 = 1 := norm_sq_one hu
  have hcoord : 1 / 2 < |u 0| ∨ 1 / 2 < |u 1| := by
    by_contra hc
    push Not at hc
    obtain ⟨hc0, hc1⟩ := hc
    nlinarith [sq_abs (u 0), sq_abs (u 1), abs_nonneg (u 0), abs_nonneg (u 1)]
  set s : ℝ := max (max (2 * r) M) 0 + 1 with hs
  have hs0 : 0 < s := by have := le_max_right (max (2 * r) M) 0; simp only [hs]; linarith
  have hsr : 2 * r < s := by
    have h1 := le_max_left (2 * r) M
    have h2 := le_max_left (max (2 * r) M) 0
    simp only [hs]; linarith
  have hsM : M < s := by
    have h1 := le_max_right (2 * r) M
    have h2 := le_max_left (max (2 * r) M) 0
    simp only [hs]; linarith
  have hfwd : fwd u (s • u) = s := by
    rw [fwd_eq]
    simp only [Plane.smul_apply]
    linear_combination s * hnorm
  have habs : ∀ i : Fin 2, |(s • u) i| = s * |u i| := fun i => by
    rw [Plane.smul_apply, abs_mul, abs_of_pos hs0]
  refine ⟨s • u, ?_, by rw [hfwd]; exact hsM⟩
  rcases hcoord with h | h
  · exact Or.inl (by rw [habs 0]; nlinarith [mul_lt_mul_of_pos_left h hs0])
  · exact Or.inr (by rw [habs 1]; nlinarith [mul_lt_mul_of_pos_left h hs0])

 

 
private theorem zmod_two_ne_add_one (x : ZMod 2) : x ≠ x + 1 := by revert x; decide

 
private theorem zmod_two_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert h; revert x; decide

 
private theorem comp_eq_of_isPreconnected {F S : Set Plane} (hS : IsPreconnected S) (hSF : S ⊆ F)
    {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) :
    connectedComponentIn F x = connectedComponentIn F y :=
  connectedComponentIn_eq (hS.subset_connectedComponentIn hx hSF hy)

 
private theorem comp_disjoint {F : Set Plane} {x y : Plane}
    (h : connectedComponentIn F x ≠ connectedComponentIn F y) :
    Disjoint (connectedComponentIn F x) (connectedComponentIn F y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact h ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

namespace ClosedPolygon

variable {P : ClosedPolygon m}

theorem isClosed_carrier (P : ClosedPolygon m) : IsClosed P.carrier :=
  P.isCompact_carrier.isClosed

theorem isOpen_compl_carrier (P : ClosedPolygon m) : IsOpen P.carrierᶜ :=
  P.isClosed_carrier.isOpen_compl

theorem carrier_nonempty (P : ClosedPolygon m) : P.carrier.Nonempty :=
  ⟨P.vertex 0, vertex_mem_carrier⟩

theorem sideL_subset_compl (D : StripData P) : D.sideL ⊆ P.carrierᶜ :=
  fun _ hz => Set.disjoint_left.1 D.sideL_disjoint_carrier hz

theorem sideR_subset_compl (D : StripData P) : D.sideR ⊆ P.carrierᶜ :=
  fun _ hz => Set.disjoint_left.1 D.sideR_disjoint_carrier hz

 


theorem det_tang_ne_zero {u : Plane} (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2)
    (i : ZMod (m + 3)) : det (P.tang i) u ≠ 0 := by
  have hne : hgt u (P.vertex i) ≠ hgt u (P.vertex (i + 1)) := hL _ (P.mem_pieces i)
  have hsub : det u (P.vertex (i + 1) - P.vertex i) ≠ 0 := by
    rw [show det u (P.vertex (i + 1) - P.vertex i) = hgt u (P.vertex (i + 1) - P.vertex i) from rfl,
      hgt_sub, sub_ne_zero]
    exact Ne.symm hne
  rw [← len_smul_tang, det_smul_right] at hsub
  intro hz
  exact hsub (by rw [det_comm, hz, neg_zero, mul_zero])

 











 


theorem exists_opposite_parity_sides (P : ClosedPolygon m) (D : StripData P)
    (i : ZMod (m + 3)) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∃ zL ∈ D.sideL, ∃ zR ∈ D.sideR, parity u P.pieces zL ≠ parity u P.pieces zR := by
  have h4 := D.four_lam_lt_len i
  have hlam := D.lam_pos
  have hlen : 0 < P.len i := len_pos
  have hlow : 2 * D.lam ≤ P.len i / 2 := by linarith
  have hhigh : P.len i / 2 ≤ P.len i - 2 * D.lam := by linarith
  have hηpos : 0 < min D.lam D.rho := lt_min hlam D.rho_pos
  obtain ⟨-, hsides, -, -⟩ := D.local_two_sided (i := i) hlow hhigh hηpos le_rfl
  
  have hmid : P.vertex i + ((P.len i / 2) / P.len i) • (P.vertex (i + 1) - P.vertex i)
      = P.pt i (P.len i / 2) := by
    rw [← len_smul_tang, smul_smul, div_mul_cancel₀ _ hlen.ne', pt_eq]
  have hp : P.pt i (P.len i / 2) ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) := by
    rw [openSegment_eq_image' ℝ]
    exact ⟨(P.len i / 2) / P.len i,
      ⟨div_pos (by linarith) hlen, by rw [div_lt_one hlen]; linarith⟩, hmid⟩
  obtain ⟨δ, hδ, hflip⟩ := P.parity_flip_carrier hu hL i hp
  have ht0 : 0 < min (δ / 2) (min D.lam D.rho / 2) := lt_min (by linarith) (by linarith)
  have htδ : min (δ / 2) (min D.lam D.rho / 2) < δ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htη : min (δ / 2) (min D.lam D.rho / 2) < min D.lam D.rho :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set t : ℝ := min (δ / 2) (min D.lam D.rho / 2)
  obtain ⟨hbef, haft, hpar⟩ := hflip t ht0 htδ
  
  have hball : ∀ r : ℝ, |r| < min D.lam D.rho →
      P.pt i (P.len i / 2) + r • u ∈ ball (P.pt i (P.len i / 2)) (min D.lam D.rho) := by
    intro r hr
    rw [mem_ball, dist_eq_norm,
      show P.pt i (P.len i / 2) + r • u - P.pt i (P.len i / 2) = r • u by abel,
      norm_smul, Real.norm_eq_abs, hu.norm, mul_one]
    exact hr
  have hbaft := hball t (by rw [abs_of_pos ht0]; exact htη)
  have hbbef : P.pt i (P.len i / 2) - t • u ∈ ball (P.pt i (P.len i / 2)) (min D.lam D.rho) := by
    have h := hball (-t) (by rw [abs_of_neg (by linarith), neg_neg]; exact htη)
    rwa [neg_smul, ← sub_eq_add_neg] at h
  
  have hkey : ∀ r : ℝ, coordAcross (P.vertex i) (P.tang i) (P.pt i (P.len i / 2) + r • u)
      = r * det (P.tang i) u := by
    intro r
    rw [coordAcross, show P.pt i (P.len i / 2) + r • u - P.vertex i
        = (P.len i / 2) • P.tang i + r • u by rw [pt_eq]; module,
      det_add_right, det_smul_right, det_self, mul_zero, zero_add, det_smul_right]
  have hcaaft := hkey t
  have hcabef : coordAcross (P.vertex i) (P.tang i) (P.pt i (P.len i / 2) - t • u)
      = -(t * det (P.tang i) u) := by
    have h := hkey (-t)
    rw [neg_smul, ← sub_eq_add_neg] at h
    rw [h]; ring
  have hsaft := hsides _ hbaft haft
  have hsbef := hsides _ hbbef hbef
  rcases lt_or_gt_of_ne (det_tang_ne_zero hL i) with hneg | hpos
  · 
    have hlt : t * det (P.tang i) u < 0 := mul_neg_of_pos_of_neg ht0 hneg
    refine ⟨P.pt i (P.len i / 2) - t • u, ?_, P.pt i (P.len i / 2) + t • u, ?_, ?_⟩
    · rcases hsbef with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hcabef] at h; linarith
    · rcases hsaft with ⟨h, -⟩ | ⟨-, h⟩
      · rw [hcaaft] at h; linarith
      · exact h
    · rw [hpar]; exact Ne.symm (zmod_two_ne_add_one _)
  · have hgt0 : 0 < t * det (P.tang i) u := mul_pos ht0 hpos
    refine ⟨P.pt i (P.len i / 2) + t • u, ?_, P.pt i (P.len i / 2) - t • u, ?_, ?_⟩
    · rcases hsaft with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hcaaft] at h; linarith
    · rcases hsbef with ⟨h, -⟩ | ⟨-, h⟩
      · rw [hcabef] at h; linarith
      · exact h
    · rw [hpar]; exact zmod_two_ne_add_one _

 
theorem parity_eq_of_mem_sideL (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideL) : parity u P.pieces x = parity u P.pieces y :=
  parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces D.isConnected_sideL.isPreconnected
    (fun z hz => by rw [P.cover_pieces]; exact sideL_subset_compl D hz) hx hy

 
theorem parity_eq_of_mem_sideR (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideR) (hy : y ∈ D.sideR) : parity u P.pieces x = parity u P.pieces y :=
  parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces D.isConnected_sideR.isPreconnected
    (fun z hz => by rw [P.cover_pieces]; exact sideR_subset_compl D hz) hx hy

 


theorem parity_ne_of_mem_sides (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideR) : parity u P.pieces x ≠ parity u P.pieces y := by
  obtain ⟨zL, hzL, zR, hzR, hne⟩ := P.exists_opposite_parity_sides D 0 hu hL
  rw [P.parity_eq_of_mem_sideL D hu hL hx hzL, P.parity_eq_of_mem_sideR D hu hL hy hzR]
  exact hne

 
theorem connectedComponentIn_ne_of_mem_sides (P : ClosedPolygon m) (D : StripData P) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideR) :
    connectedComponentIn P.carrierᶜ x ≠ connectedComponentIn P.carrierᶜ y := by
  obtain ⟨u, hu, hL⟩ := P.exists_direction_pieces
  intro heq
  refine P.parity_ne_of_mem_sides D hu hL hx hy ?_
  have hxc : x ∈ connectedComponentIn P.carrierᶜ y := by
    rw [← heq]; exact mem_connectedComponentIn (sideL_subset_compl D hx)
  exact P.parity_eq_of_mem_connectedComponentIn_carrier hu hL (sideR_subset_compl D hy) hxc

 





 


theorem exists_mem_sides_connectedComponentIn (P : ClosedPolygon m) (D : StripData P) {x : Plane}
    (hx : x ∉ P.carrier) :
    ∃ y ∈ D.sideL ∪ D.sideR,
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ y := by
  
  obtain ⟨a, haC, hmin⟩ := P.isCompact_carrier.exists_isMinOn P.carrier_nonempty
    (continuous_const.dist continuous_id).continuousOn
  have hmin' : ∀ b ∈ P.carrier, dist x a ≤ dist x b := isMinOn_iff.1 hmin
  have hax : a ≠ x := fun h => hx (h ▸ haC)
  have hvne : a - x ≠ 0 := sub_ne_zero.2 hax
  have hvpos : 0 < ‖a - x‖ := norm_pos_iff.2 hvne
  have hcont : Continuous (fun θ : ℝ => x + θ • (a - x)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  
  have hoff : ∀ θ : ℝ, θ ∈ Ico (0 : ℝ) 1 → x + θ • (a - x) ∉ P.carrier := by
    intro θ hθ
    refine Plane.notMem_of_mem_segment_of_isMinOn haC hx hmin' ?_ ?_
    · rw [segment_eq_image' ℝ x a]; exact ⟨θ, ⟨hθ.1, hθ.2.le⟩, rfl⟩
    · intro h
      have h0 : (θ - 1) • (a - x) = 0 := by linear_combination (norm := module) h
      rcases smul_eq_zero.1 h0 with h1 | h1
      · have := hθ.2; linarith
      · exact hvne h1
  have hSΩ : (fun θ : ℝ => x + θ • (a - x)) '' Ico 0 1 ⊆ P.carrierᶜ := by
    rintro z ⟨θ, hθ, rfl⟩
    exact hoff θ hθ
  have hSpre : IsPreconnected ((fun θ : ℝ => x + θ • (a - x)) '' Ico 0 1) :=
    isPreconnected_Ico.image _ hcont.continuousOn
  
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.1 D.isOpen_nbhd a (D.carrier_subset_nbhd haC)
  have hmpos : 0 < min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) := lt_min (by norm_num) (by positivity)
  have hmhalf : min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) ≤ 1 / 2 := min_le_left _ _
  have hθmem : (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) ∈ Ico (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hprod : ε / (2 * ‖a - x‖) * ‖a - x‖ = ε / 2 := by
    field_simp
  have hdist : dist (x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x)) a < ε := by
    rw [dist_eq_norm, show x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x) - a
        = (-(min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)))) • (a - x) by module,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hmpos]
    calc min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) * ‖a - x‖
        ≤ ε / (2 * ‖a - x‖) * ‖a - x‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) hvpos.le
      _ = ε / 2 := hprod
      _ < ε := by linarith
  set y : Plane := x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x) with hy
  have hyLR : y ∈ D.sideL ∪ D.sideR := by
    rw [← D.nbhd_diff_carrier]
    exact ⟨hεball (mem_ball.2 hdist), hoff _ hθmem⟩
  exact ⟨y, hyLR, comp_eq_of_isPreconnected hSpre hSΩ ⟨0, ⟨le_rfl, one_pos⟩, by simp⟩
    ⟨_, hθmem, hy.symm⟩⟩

 


theorem connectedComponentIn_eq_of_notMem (P : ClosedPolygon m) (D : StripData P)
    {zL zR : Plane} (hzL : zL ∈ D.sideL) (hzR : zR ∈ D.sideR) {x : Plane} (hx : x ∉ P.carrier) :
    connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zL ∨
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zR := by
  obtain ⟨y, hy, hyx⟩ := P.exists_mem_sides_connectedComponentIn D hx
  rcases hy with hy | hy
  · exact Or.inl (hyx.trans (comp_eq_of_isPreconnected D.isConnected_sideL.isPreconnected
      (sideL_subset_compl D) hy hzL))
  · exact Or.inr (hyx.trans (comp_eq_of_isPreconnected D.isConnected_sideR.isPreconnected
      (sideR_subset_compl D) hy hzR))

end ClosedPolygon

 









 

private theorem inside_outside_of_two_components {C : Set Plane} {r : ℝ} {z₁ z₂ : Plane}
    (hne : connectedComponentIn Cᶜ z₁ ≠ connectedComponentIn Cᶜ z₂)
    (hall : ∀ x ∉ C, connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₁ ∨
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₂)
    (hbey : Plane.beyondSquare r ⊆ connectedComponentIn Cᶜ z₂) :
    inside C = connectedComponentIn Cᶜ z₁ ∧ outside C = connectedComponentIn Cᶜ z₂ := by
  have hdisj := comp_disjoint hne
  
  have h1sq : connectedComponentIn Cᶜ z₁ ⊆ Plane.closedSquare 0 r := by
    intro w hw
    by_contra hwq
    exact Set.disjoint_left.1 hdisj hw (hbey (by rw [Plane.beyondSquare_eq_compl]; exact hwq))
  have h1bdd : IsBounded (connectedComponentIn Cᶜ z₁) := (isBounded_closedSquare r).subset h1sq
  have h2unb : ¬ IsBounded (connectedComponentIn Cᶜ z₂) := fun hb =>
    not_isBounded_beyondSquare r (hb.subset hbey)
  constructor
  · ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rcases hall w hw.1 with h | h
      · rw [← h]; exact mem_connectedComponentIn hw.1
      · exact absurd (h ▸ hw.2) h2unb
    · refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
      rw [← connectedComponentIn_eq hw]
      exact h1bdd
  · ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rcases hall w hw.1 with h | h
      · exact absurd (h ▸ h1bdd) hw.2
      · rw [← h]; exact mem_connectedComponentIn hw.1
    · refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
      rw [← connectedComponentIn_eq hw]
      exact h2unb

 


private theorem frontier_connectedComponentIn_eq {C : Set Plane} (hC : IsClosed C) (z : Plane)
    (hcl : C ⊆ closure (connectedComponentIn Cᶜ z)) :
    frontier (connectedComponentIn Cᶜ z) = C := by
  refine Set.Subset.antisymm (Plane.frontier_connectedComponentIn_compl_subset hC z) fun w hw => ?_
  rw [(Plane.isOpen_connectedComponentIn hC.isOpen_compl).frontier_eq]
  exact ⟨hcl hw, fun hmem => connectedComponentIn_subset _ _ hmem hw⟩

 


private theorem isSeparating_of_two_components {C : Set Plane} (hJ : IsJordanCurve C)
    (hC : IsClosed C) {r : ℝ} {z₁ z₂ : Plane} (h₁ : z₁ ∉ C) (h₂ : z₂ ∉ C)
    (hne : connectedComponentIn Cᶜ z₁ ≠ connectedComponentIn Cᶜ z₂)
    (hall : ∀ x ∉ C, connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₁ ∨
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₂)
    (hcl₁ : C ⊆ closure (connectedComponentIn Cᶜ z₁))
    (hcl₂ : C ⊆ closure (connectedComponentIn Cᶜ z₂))
    (hbey : Plane.beyondSquare r ⊆ connectedComponentIn Cᶜ z₂) :
    IsSeparating C := by
  obtain ⟨hin, hout⟩ := inside_outside_of_two_components hne hall hbey
  refine ⟨hJ, ?_, ?_, ?_, ?_⟩
  · rw [hin]; exact ⟨⟨z₁, mem_connectedComponentIn h₁⟩, isPreconnected_connectedComponentIn⟩
  · rw [hout]; exact ⟨⟨z₂, mem_connectedComponentIn h₂⟩, isPreconnected_connectedComponentIn⟩
  · rw [hin]; exact frontier_connectedComponentIn_eq hC z₁ hcl₁
  · rw [hout]; exact frontier_connectedComponentIn_eq hC z₂ hcl₂

namespace ClosedPolygon

variable {P : ClosedPolygon m}

 






theorem isSeparating_carrier (P : ClosedPolygon m) : IsSeparating P.carrier := by
  obtain ⟨D⟩ := exists_stripData P
  obtain ⟨zL, hzL⟩ := D.isConnected_sideL.nonempty
  obtain ⟨zR, hzR⟩ := D.isConnected_sideR.nonempty
  have hzLC : zL ∉ P.carrier := sideL_subset_compl D hzL
  have hzRC : zR ∉ P.carrier := sideR_subset_compl D hzR
  have hne := P.connectedComponentIn_ne_of_mem_sides D hzL hzR
  have hall : ∀ x ∉ P.carrier, connectedComponentIn P.carrierᶜ x =
      connectedComponentIn P.carrierᶜ zL ∨
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zR :=
    fun x hx => P.connectedComponentIn_eq_of_notMem D hzL hzR hx
  
  have hsubL : D.sideL ⊆ connectedComponentIn P.carrierᶜ zL :=
    D.isConnected_sideL.isPreconnected.subset_connectedComponentIn hzL (sideL_subset_compl D)
  have hsubR : D.sideR ⊆ connectedComponentIn P.carrierᶜ zR :=
    D.isConnected_sideR.isPreconnected.subset_connectedComponentIn hzR (sideR_subset_compl D)
  have hclL : P.carrier ⊆ closure (connectedComponentIn P.carrierᶜ zL) :=
    subset_trans D.carrier_subset_closure_sideL (closure_mono hsubL)
  have hclR : P.carrier ⊆ closure (connectedComponentIn P.carrierᶜ zR) :=
    subset_trans D.carrier_subset_closure_sideR (closure_mono hsubR)
  
  obtain ⟨r, -, hrC⟩ := Plane.IsCompact.exists_closedSquare P.isCompact_carrier
  have hbeyC : Plane.beyondSquare r ⊆ P.carrierᶜ := by
    rw [Plane.beyondSquare_eq_compl]; exact compl_subset_compl.2 hrC
  obtain ⟨w, hw⟩ := (Plane.isConnected_beyondSquare r).nonempty
  have hbeysub : Plane.beyondSquare r ⊆ connectedComponentIn P.carrierᶜ w :=
    (Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn hw hbeyC
  rcases hall w (hbeyC hw) with hcw | hcw
  · exact isSeparating_of_two_components P.isJordanCurve_carrier P.isClosed_carrier hzRC hzLC
      (Ne.symm hne) (fun x hx => (hall x hx).symm) hclR hclL (hcw ▸ hbeysub)
  · exact isSeparating_of_two_components P.isJordanCurve_carrier P.isClosed_carrier hzLC hzRC
      hne hall hclL hclR (hcw ▸ hbeysub)

 

theorem connectedComponentIn_eq_inside_or_outside (P : ClosedPolygon m) {x : Plane}
    (hx : x ∉ P.carrier) :
    connectedComponentIn P.carrierᶜ x = inside P.carrier ∨
      connectedComponentIn P.carrierᶜ x = outside P.carrier := by
  have h : x ∈ inside P.carrier ∪ outside P.carrier := by rw [inside_union_outside]; exact hx
  rcases h with h | h
  · exact Or.inl (P.isSeparating_carrier.connectedComponentIn_eq_inside h)
  · exact Or.inr (P.isSeparating_carrier.connectedComponentIn_eq_outside h)

 







 
theorem parity_eq_zero_of_mem_outside (P : ClosedPolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2)
    {x : Plane} (hx : x ∈ outside P.carrier) : parity u P.pieces x = 0 := by
  obtain ⟨r, -, hrC⟩ := Plane.IsCompact.exists_closedSquare P.isCompact_carrier
  obtain ⟨R, hR⟩ := P.isCompact_carrier.isBounded.subset_closedBall (0 : Plane)
  obtain ⟨q, hqbey, hqfwd⟩ := exists_beyond_of_fwd_lt hu r R
  have hbeyC : Plane.beyondSquare r ⊆ P.carrierᶜ := by
    rw [Plane.beyondSquare_eq_compl]; exact compl_subset_compl.2 hrC
  
  have hq0 : parity u P.pieces q = 0 := by
    refine parity_eq_zero_of_lt hL fun z hz => ?_
    rw [P.cover_pieces] at hz
    have h1 : ‖z‖ ≤ R := by simpa using hR hz
    have h2 : fwd u z ≤ R := le_trans (le_trans (le_abs_self _) (abs_fwd_le_norm hu z)) h1
    linarith
  
  have hqout : q ∈ outside P.carrier :=
    ⟨hbeyC hqbey, fun hb => not_isBounded_beyondSquare r (hb.subset
      ((Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn
        hqbey hbeyC))⟩
  rw [← hq0]
  exact parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces
    P.isSeparating_carrier.isConnected_outside.isPreconnected
    (fun z hz => by rw [P.cover_pieces]; exact hz.1) hx hqout

 


theorem parity_eq_one_of_mem_inside (P : ClosedPolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2)
    {x : Plane} (hx : x ∈ inside P.carrier) : parity u P.pieces x = 1 := by
  obtain ⟨D⟩ := exists_stripData P
  obtain ⟨zL, hzL⟩ := D.isConnected_sideL.nonempty
  obtain ⟨zR, hzR⟩ := D.isConnected_sideR.nonempty
  have hpne := P.parity_ne_of_mem_sides D hu hL hzL hzR
  have hconst : ∀ y ∈ inside P.carrier, parity u P.pieces y = parity u P.pieces x :=
    fun y hy => parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces
      P.isSeparating_carrier.isConnected_inside.isPreconnected
      (fun z hz => by rw [P.cover_pieces]; exact hz.1) hy hx
  have hmemL : zL ∈ inside P.carrier ∪ outside P.carrier := by
    rw [inside_union_outside]; exact sideL_subset_compl D hzL
  have hmemR : zR ∈ inside P.carrier ∪ outside P.carrier := by
    rw [inside_union_outside]; exact sideR_subset_compl D hzR
  refine zmod_two_eq_one_of_ne_zero ?_
  rcases hmemL with h | h <;> rcases hmemR with h' | h'
  · exact absurd ((hconst zL h).trans (hconst zR h').symm) hpne
  · rw [← hconst zL h, ← P.parity_eq_zero_of_mem_outside hu hL h']
    exact hpne
  · rw [← hconst zR h', ← P.parity_eq_zero_of_mem_outside hu hL h]
    exact Ne.symm hpne
  · exact absurd ((P.parity_eq_zero_of_mem_outside hu hL h).trans
      (P.parity_eq_zero_of_mem_outside hu hL h').symm) hpne

 

 



theorem polygonal_jordan (P : ClosedPolygon m) :
    IsJordanCurve P.carrier ∧ IsPolygonal P.carrier ∧
      IsOpen (inside P.carrier) ∧ IsOpen (outside P.carrier) ∧
      IsConnected (inside P.carrier) ∧ IsConnected (outside P.carrier) ∧
      Disjoint (inside P.carrier) (outside P.carrier) ∧
      inside P.carrier ∪ outside P.carrier = P.carrierᶜ ∧
      IsBounded (inside P.carrier) ∧ ¬ IsBounded (outside P.carrier) ∧
      (∀ x ∉ P.carrier, connectedComponentIn P.carrierᶜ x = inside P.carrier ∨
        connectedComponentIn P.carrierᶜ x = outside P.carrier) ∧
      frontier (inside P.carrier) = P.carrier ∧ frontier (outside P.carrier) = P.carrier :=
  ⟨P.isJordanCurve_carrier, P.isPolygonal_carrier,
    P.isSeparating_carrier.isOpen_inside, P.isSeparating_carrier.isOpen_outside,
    P.isSeparating_carrier.isConnected_inside, P.isSeparating_carrier.isConnected_outside,
    disjoint_inside_outside, inside_union_outside _,
    P.isSeparating_carrier.isBounded_inside, P.isSeparating_carrier.not_isBounded_outside,
    fun _ hx => P.connectedComponentIn_eq_inside_or_outside hx,
    P.isSeparating_carrier.frontier_inside, P.isSeparating_carrier.frontier_outside⟩

end ClosedPolygon

 





theorem isSeparating_unitTriangle : IsSeparating unitTriangle.carrier :=
  unitTriangle.isSeparating_carrier

end Schoenflies
