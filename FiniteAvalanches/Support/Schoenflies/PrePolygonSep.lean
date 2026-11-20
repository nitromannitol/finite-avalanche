/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/PrePolygonSep.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Realization

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 


















































































open Bornology Metric Set

namespace Schoenflies

open Plane

 




 
private theorem ne_add_one_zmod_two (x : ZMod 2) : x ≠ x + 1 := by revert x; decide

 
private theorem eq_one_of_ne_zero_zmod_two {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert h; revert x; decide

 





section GeneralParity

variable {L : List Piece} {u : Plane}

 

private theorem isLinearMap_fwd (u : Plane) : IsLinearMap ℝ (fwd u) where
  map_add x y := by simp only [fwd_eq, Plane.add_apply]; ring
  map_smul c x := by simp only [fwd_eq, Plane.smul_apply, smul_eq_mul]; ring

 


private def farSide (u : Plane) (R : ℝ) : Set Plane := {z | R < fwd u z}

private theorem convex_farSide (u : Plane) (R : ℝ) : Convex ℝ (farSide u R) :=
  convex_halfSpace_gt (isLinearMap_fwd u) R

 
private theorem fwd_smul_self (hu : Plane.IsDirection u) (s : ℝ) : fwd u (s • u) = s := by
  have h : fwd u (s • u) = s * fwd u u := by simp only [fwd_eq, Plane.smul_apply]; ring
  rw [h, fwd_self hu, mul_one]

 
private theorem not_isBounded_farSide (hu : Plane.IsDirection u) (R : ℝ) :
    ¬ IsBounded (farSide u R) := by
  intro hb
  obtain ⟨R', hR'⟩ := hb.subset_closedBall (0 : Plane)
  set t : ℝ := max (max R R') 0 + 1 with htdef
  have h0 : 0 ≤ max (max R R') 0 := le_max_right _ _
  have hpos : 0 < t := by rw [htdef]; linarith
  have hR1 : R < t := by
    have := le_trans (le_max_left R R') (le_max_left (max R R') 0)
    rw [htdef]; linarith
  have hR2 : R' < t := by
    have := le_trans (le_max_right R R') (le_max_left (max R R') 0)
    rw [htdef]; linarith
  have hmem : t • u ∈ farSide u R := by
    change R < fwd u (t • u)
    rw [fwd_smul_self hu]; exact hR1
  have hnorm : ‖t • u‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_pos hpos]
  have := mem_closedBall_zero_iff.1 (hR' hmem)
  rw [hnorm] at this
  linarith

 






theorem parity_eq_zero_of_mem_outside_cover (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2) (hC : IsClosedChain L)
    (hsep : IsSeparating (cover L)) {x : Plane} (hx : x ∈ outside (cover L)) :
    parity u L x = 0 := by
  obtain ⟨R, hR⟩ := (isCompact_cover L).isBounded.subset_closedBall (0 : Plane)
  have hcov : ∀ z ∈ cover L, fwd u z ≤ R := fun z hz =>
    le_trans (le_trans (le_abs_self _) (abs_fwd_le_norm hu z)) (mem_closedBall_zero_iff.1 (hR hz))
  have hdisj : farSide u R ⊆ (cover L)ᶜ := fun z hz hzc => absurd (hcov z hzc) (not_le.2 hz)
  have hqf : fwd u ((R + 1) • u) = R + 1 := fwd_smul_self hu (R + 1)
  have hqmem : (R + 1) • u ∈ farSide u R := by
    change R < fwd u ((R + 1) • u)
    rw [hqf]; linarith
  
  have hqout : (R + 1) • u ∈ outside (cover L) := by
    refine ⟨hdisj hqmem, fun hb => not_isBounded_farSide hu R (hb.subset ?_)⟩
    exact (convex_farSide u R).isPreconnected.subset_connectedComponentIn hqmem hdisj
  have hq0 : parity u L ((R + 1) • u) = 0 :=
    parity_eq_zero_of_lt hL fun z hz => lt_of_le_of_lt (hcov z hz) (by rw [hqf]; linarith)
  rw [← hq0]
  exact parity_eq_of_isPreconnected hu hL hC hsep.isConnected_outside.isPreconnected
    (fun z hz => hz.1) hx hqout

 








theorem parity_eq_one_of_mem_inside_cover (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2) (hC : IsClosedChain L)
    (hsep : IsSeparating (cover L)) {a b : Plane} (ha : a ∉ cover L) (hb : b ∉ cover L)
    (hab : parity u L a ≠ parity u L b) {x : Plane} (hx : x ∈ inside (cover L)) :
    parity u L x = 1 := by
  have hzero : ∀ y ∈ outside (cover L), parity u L y = 0 := fun y hy =>
    parity_eq_zero_of_mem_outside_cover hu hL hC hsep hy
  have hconst : ∀ y ∈ inside (cover L), parity u L y = parity u L x := fun y hy =>
    parity_eq_of_isPreconnected hu hL hC hsep.isConnected_inside.isPreconnected
      (fun z hz => hz.1) hy hx
  have hma : a ∈ inside (cover L) ∪ outside (cover L) := by rw [inside_union_outside]; exact ha
  have hmb : b ∈ inside (cover L) ∪ outside (cover L) := by rw [inside_union_outside]; exact hb
  refine eq_one_of_ne_zero_zmod_two ?_
  rcases hma with h | h <;> rcases hmb with h' | h'
  · exact absurd ((hconst a h).trans (hconst b h').symm) hab
  · rw [hzero b h'] at hab
    rw [← hconst a h]
    exact hab
  · rw [hzero a h] at hab
    rw [← hconst b h']
    exact Ne.symm hab
  · exact absurd ((hzero a h).trans (hzero b h').symm) hab

end GeneralParity

namespace PrePolygon

variable {m : ℕ}

 




 

def pieces (P : PrePolygon m) : List Piece :=
  (List.range (m + 3)).map fun j : ℕ =>
    (P.vertex (j : ZMod (m + 3)), P.vertex ((j : ZMod (m + 3)) + 1))

 
@[simp] theorem pieces_toPre (P : ClosedPolygon m) : P.toPre.pieces = P.pieces := rfl

 
theorem mem_pieces (P : PrePolygon m) (i : ZMod (m + 3)) :
    (P.vertex i, P.vertex (i + 1)) ∈ P.pieces := by
  refine List.mem_map.2 ⟨i.val, List.mem_range.2 (ZMod.val_lt i), ?_⟩
  rw [ZMod.natCast_rightInverse i]

 
theorem exists_of_mem_pieces {P : PrePolygon m} {Q : Piece} (hQ : Q ∈ P.pieces) :
    ∃ i : ZMod (m + 3), Q = (P.vertex i, P.vertex (i + 1)) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hQ
  exact ⟨(j : ZMod (m + 3)), rfl⟩

 

theorem pieces_nondeg (P : PrePolygon m) : ∀ Q ∈ P.pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
  exact vertex_ne_succ i

 

theorem isClosedChain_pieces (P : PrePolygon m) : IsClosedChain P.pieces := by
  intro f
  have hmap : (P.pieces.map fun Q => f Q.1 + f Q.2)
      = (List.range (m + 3)).map fun j : ℕ =>
        f (P.vertex (j : ZMod (m + 3))) + f (P.vertex ((j + 1 : ℕ) : ZMod (m + 3))) := by
    rw [pieces, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ]
  rw [hmap]
  have key := sum_range_boundary (fun k : ℕ => f (P.vertex (k : ZMod (m + 3)))) (m + 3)
  rw [key, Nat.cast_zero, ZMod.natCast_self]
  exact add_self_zmod_two _

 

theorem cover_pieces (P : PrePolygon m) : cover P.pieces = P.carrier := by
  apply Set.Subset.antisymm
  · rw [cover]
    refine Set.iUnion₂_subset fun Q hQ => ?_
    obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
    exact Set.subset_iUnion (fun i => P.edge i) i
  · refine Set.iUnion_subset fun i => ?_
    exact fun z hz => mem_cover (P.mem_pieces i) hz

 
theorem pieces_nodup (P : PrePolygon m) : P.pieces.Nodup := by
  rw [pieces]
  refine List.Nodup.map_on (fun j hj k hk heq => ?_) List.nodup_range
  exact ClosedPolygon.natCast_inj (List.mem_range.1 hj) (List.mem_range.1 hk)
    (P.vertex_inj (congrArg Prod.fst heq))

 




 
theorem isCompact_carrier (P : PrePolygon m) : IsCompact P.carrier := by
  rw [← P.cover_pieces]; exact isCompact_cover _

theorem isClosed_carrier (P : PrePolygon m) : IsClosed P.carrier := P.isCompact_carrier.isClosed

 

theorem isJordanCurve_carrier (P : PrePolygon m) : IsJordanCurve P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isJordanCurve_carrier

 
theorem isPolygonal_carrier (P : PrePolygon m) : IsPolygonal P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isPolygonal_carrier

 





theorem isSeparating_carrier (P : PrePolygon m) : IsSeparating P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isSeparating_carrier

 

theorem connectedComponentIn_eq_inside_or_outside (P : PrePolygon m) {x : Plane}
    (hx : x ∉ P.carrier) :
    connectedComponentIn P.carrierᶜ x = inside P.carrier ∨
      connectedComponentIn P.carrierᶜ x = outside P.carrier := by
  have h : x ∈ inside P.carrier ∪ outside P.carrier := by rw [inside_union_outside]; exact hx
  rcases h with h | h
  · exact Or.inl (P.isSeparating_carrier.connectedComponentIn_eq_inside h)
  · exact Or.inr (P.isSeparating_carrier.connectedComponentIn_eq_outside h)

 



 

theorem exists_direction_pieces (P : PrePolygon m) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
  exists_direction_hgt_ne P.pieces P.pieces_nondeg

 

theorem parity_eq_of_mem_connectedComponentIn_carrier (P : PrePolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∈ connectedComponentIn P.carrierᶜ x) :
    parity u P.pieces y = parity u P.pieces x := by
  rw [← P.cover_pieces] at hx hy
  exact parity_eq_of_mem_connectedComponentIn hu hL P.isClosedChain_pieces hx hy

 

theorem notMem_edge_of_mem_openSegment {P : PrePolygon m} {i j : ZMod (m + 3)} (hij : j ≠ i)
    {p : Plane} (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) : p ∉ P.edge j := by
  intro hpj
  have hmem := P.edges_meet i j (Ne.symm hij)
    (Set.mem_inter (openSegment_subset_segment ℝ _ _ hp) hpj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl
  · exact vertex_ne_succ i (left_mem_openSegment_iff.1 hp)
  · exact vertex_ne_succ i (right_mem_openSegment_iff.1 hp)

 






theorem parity_flip_carrier (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (i : ZMod (m + 3)) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ P.carrier ∧ p + t • u ∉ P.carrier ∧
        parity u P.pieces (p - t • u) = parity u P.pieces (p + t • u) + 1 := by
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem (P.mem_pieces i)
  
  have hnodup := P.pieces_nodup
  rw [hsplit, List.nodup_append] at hnodup
  obtain ⟨-, hnd2, hdisj⟩ := hnodup
  have hQ₁ : (P.vertex i, P.vertex (i + 1)) ∉ L₁ := fun hmem => hdisj _ hmem _ (by simp) rfl
  have hQ₂ : (P.vertex i, P.vertex (i + 1)) ∉ L₂ := (List.nodup_cons.1 hnd2).1
  have hmiss : ∀ R ∈ L₁ ++ L₂, p ∉ Piece.seg R := by
    intro R hR
    have hRne : R ≠ (P.vertex i, P.vertex (i + 1)) := by
      rcases List.mem_append.1 hR with h | h
      · exact fun heq => hQ₁ (heq ▸ h)
      · exact fun heq => hQ₂ (heq ▸ h)
    have hRmem : R ∈ P.pieces := by
      rw [hsplit]
      rcases List.mem_append.1 hR with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    obtain ⟨j, rfl⟩ := exists_of_mem_pieces hRmem
    exact notMem_edge_of_mem_openSegment (fun heq => hRne (by rw [heq])) hp
  
  
  have h1 : p ∉ cover L₁ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_left _ hR) hpR
  have h2 : p ∉ cover L₂ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_right _ hR) hpR
  have hL' : ∀ R ∈ L₁ ++ (P.vertex i, P.vertex (i + 1)) :: L₂, hgt u R.1 ≠ hgt u R.2 := by
    rw [← hsplit]; exact hL
  obtain ⟨δ, hδ, hmain⟩ := parity_flip hu hL' hp h1 h2
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := hmain t ht htδ
  rw [← hsplit] at ha hb hc
  rw [P.cover_pieces] at ha hb
  exact ⟨ha, hb, hc⟩

 

theorem exists_parity_ne (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∃ a b : Plane, a ∉ P.carrier ∧ b ∉ P.carrier ∧
      parity u P.pieces a ≠ parity u P.pieces b := by
  have hpmem : (1 / 2 : ℝ) • P.vertex 0 + (1 / 2 : ℝ) • P.vertex 1
      ∈ openSegment ℝ (P.vertex 0) (P.vertex (0 + 1)) := by
    rw [zero_add]
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  obtain ⟨δ, hδ, hmain⟩ := P.parity_flip_carrier hu hL 0 hpmem
  obtain ⟨h1, h2, h3⟩ := hmain (δ / 2) (by linarith) (by linarith)
  refine ⟨_, _, h1, h2, fun hh => ?_⟩
  rw [h3] at hh
  exact ne_add_one_zmod_two _ hh.symm

 

theorem parity_eq_zero_of_mem_outside (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ outside P.carrier) :
    parity u P.pieces x = 0 := by
  have hcov := P.cover_pieces
  refine parity_eq_zero_of_mem_outside_cover hu hL P.isClosedChain_pieces ?_ ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact hx

 

theorem parity_eq_one_of_mem_inside (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ inside P.carrier) :
    parity u P.pieces x = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := P.exists_parity_ne hu hL
  have hcov := P.cover_pieces
  refine parity_eq_one_of_mem_inside_cover (a := a) (b := b) hu hL P.isClosedChain_pieces
    ?_ ?_ ?_ hab ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact ha
  · rw [hcov]; exact hb
  · rw [hcov]; exact hx

 

theorem parity_eq_one_iff (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∉ P.carrier) :
    parity u P.pieces x = 1 ↔ x ∈ inside P.carrier := by
  have hmem : x ∈ inside P.carrier ∪ outside P.carrier := by
    rw [inside_union_outside]; exact hx
  refine ⟨fun h1 => ?_, P.parity_eq_one_of_mem_inside hu hL⟩
  rcases hmem with h | h
  · exact h
  · rw [P.parity_eq_zero_of_mem_outside hu hL h] at h1
    exact absurd h1 (by decide)

 
theorem parity_eq_zero_iff (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∉ P.carrier) :
    parity u P.pieces x = 0 ↔ x ∈ outside P.carrier := by
  have hmem : x ∈ inside P.carrier ∪ outside P.carrier := by
    rw [inside_union_outside]; exact hx
  refine ⟨fun h0 => ?_, P.parity_eq_zero_of_mem_outside hu hL⟩
  rcases hmem with h | h
  · rw [P.parity_eq_one_of_mem_inside hu hL h] at h0
    exact absurd h0 (by decide)
  · exact h

end PrePolygon

 







example {m : ℕ} (P : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ outside P.carrier) :
    parity u P.pieces x = 0 := by
  have hcov := P.cover_pieces
  refine parity_eq_zero_of_mem_outside_cover hu hL P.isClosedChain_pieces ?_ ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact hx

example {m : ℕ} (P : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ inside P.carrier) :
    parity u P.pieces x = 1 := by
  
  obtain ⟨a, b, ha, hb, hab⟩ := P.toPre.exists_parity_ne hu hL
  have hcov := P.cover_pieces
  refine parity_eq_one_of_mem_inside_cover (a := a) (b := b) hu hL P.isClosedChain_pieces
    ?_ ?_ ?_ hab ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact ha
  · rw [hcov]; exact hb
  · rw [hcov]; exact hx

end Schoenflies
