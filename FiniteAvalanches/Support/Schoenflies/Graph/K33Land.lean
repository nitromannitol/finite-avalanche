/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/K33Land.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.PrePolygonArc
import FiniteAvalanches.Support.Schoenflies.Graph.K33Closed

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 























































































open Bornology Metric Set unitInterval
open scoped Graph

namespace Schoenflies

open Plane

namespace PrePolygon

 







 


theorem exists_splice {m m' : ℕ} (P : PrePolygon m) (P' : PrePolygon m')
    {a : ZMod (m + 3)} {k : ℕ} {b : ZMod (m' + 3)} {l : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) (hl1 : 1 ≤ l) (hl2 : l ≤ m' + 2)
    (hstart : P'.vertex b = P.vertex (a + (k : ZMod (m + 3))))
    (hend : P'.vertex (b + (l : ZMod (m' + 3))) = P.vertex a)
    (hinter : P.arc a k ∩ P'.arc b l = {P.vertex a, P.vertex (a + (k : ZMod (m + 3)))}) :
    ∃ (n : ℕ) (Q : PrePolygon n), Q.pieces = P.arcPieces a k ++ P'.arcPieces b l := by
  
  have hthree : 3 ≤ k + l := by
    by_contra hcon
    obtain rfl : k = 1 := by omega
    obtain rfl : l = 1 := by omega
    rw [Nat.cast_one] at hstart hinter
    rw [Nat.cast_one] at hend
    have hseg : P'.edge b = P.edge a := by
      rw [edge, edge, hstart, hend, segment_symm]
    rw [P.arc_one a, P'.arc_one b, hseg, Set.inter_self] at hinter
    obtain ⟨z, hz, hz1, hz2⟩ := exists_mem_segment_ne (vertex_ne_succ (P := P) a)
    rcases hinter.subset hz with h | h
    exacts [hz1 h, hz2 h]
  obtain ⟨n, hn⟩ : ∃ n, k + l = n + 3 := ⟨k + l - 3, by omega⟩
  
  have hPedge : ∀ t : ℕ, t < k → P.edge (a + (t : ZMod (m + 3))) ⊆ P.arc a k :=
    fun t ht z hz => mem_arc_iff.2 ⟨t, ht, hz⟩
  have hP'edge : ∀ t : ℕ, t < l → P'.edge (b + (t : ZMod (m' + 3))) ⊆ P'.arc b l :=
    fun t ht z hz => mem_arc_iff.2 ⟨t, ht, hz⟩
  have hcross : ∀ s : ℕ, s < k → ∀ t : ℕ, t < l →
      P.edge (a + (s : ZMod (m + 3))) ∩ P'.edge (b + (t : ZMod (m' + 3)))
        ⊆ ({P.vertex a, P.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
    intro s hs t ht z hz
    rw [← hinter]
    exact ⟨hPedge s hs hz.1, hP'edge t ht hz.2⟩
  
  set w : ZMod (n + 3) → Plane := fun j =>
    if j.val < k then P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)))
    else P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))) with hwdef
  have hbound : ∀ j : ZMod (n + 3), j.val < k + l := fun j => by
    have := ZMod.val_lt j; omega
  have hw_lt : ∀ j : ZMod (n + 3), j.val < k →
      w j = P.vertex (a + ((j.val : ℕ) : ZMod (m + 3))) := fun j hj => by
    rw [hwdef]; exact if_pos hj
  have hw_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      w j = P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))) := fun j hj => by
    rw [hwdef]; exact if_neg hj
  have hsucc_lt : ∀ j : ZMod (n + 3), j.val < k →
      w (j + 1) = P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)) + 1) := by
    intro j hj
    have hval : (j + 1).val = j.val + 1 := val_succ_of_lt (m := n) (by omega)
    by_cases hlt : j.val + 1 < k
    · rw [hw_lt (j + 1) (by omega), hval]
      congr 1
      push_cast
      ring
    · have hk' : j.val + 1 = k := by omega
      rw [hw_ge (j + 1) (by omega), hval, hk', Nat.sub_self, Nat.cast_zero, add_zero, hstart]
      congr 1
      rw [← hk']
      push_cast
      ring
  have hsucc_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      w (j + 1) = P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3)) + 1) := by
    intro j hj
    have hjb := hbound j
    by_cases hlt : j.val + 1 < n + 3
    · have hval : (j + 1).val = j.val + 1 := val_succ_of_lt (m := n) (by omega)
      rw [hw_ge (j + 1) (by omega), hval]
      congr 1
      rw [show j.val + 1 - k = (j.val - k) + 1 by omega]
      push_cast
      ring
    · have hval : (j + 1).val = 0 := val_succ_last (m := n) (by omega)
      rw [hw_lt (j + 1) (by omega), hval, Nat.cast_zero, add_zero, ← hend]
      congr 1
      have hc : ((l - 1 : ℕ) : ZMod (m' + 3)) + 1 = ((l : ℕ) : ZMod (m' + 3)) :=
        ClosedPolygon.natCast_pred_succ (by omega)
      rw [show j.val - k = l - 1 by omega, add_assoc, hc]
  
  have hE_lt : ∀ j : ZMod (n + 3), j.val < k →
      segment ℝ (w j) (w (j + 1)) = P.edge (a + ((j.val : ℕ) : ZMod (m + 3))) := by
    intro j hj
    rw [hw_lt j hj, hsucc_lt j hj, edge]
  have hE_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      segment ℝ (w j) (w (j + 1)) = P'.edge (b + ((j.val - k : ℕ) : ZMod (m' + 3))) := by
    intro j hj
    rw [hw_ge j hj, hsucc_ge j hj, edge]
  have hends_lt : ∀ j : ZMod (n + 3), j.val < k →
      ({w j, w (j + 1)} : Set Plane)
        = {P.vertex (a + ((j.val : ℕ) : ZMod (m + 3))),
           P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)) + 1)} := by
    intro j hj
    rw [hw_lt j hj, hsucc_lt j hj]
  have hends_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      ({w j, w (j + 1)} : Set Plane)
        = {P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))),
           P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3)) + 1)} := by
    intro j hj
    rw [hw_ge j hj, hsucc_ge j hj]
  refine ⟨n, ⟨w, ?_, ?_⟩, ?_⟩
  · 
    intro i j hij
    have hib := hbound i
    have hjb := hbound j
    have hcase : ∀ i' j' : ZMod (n + 3), i'.val < k → ¬ j'.val < k → w i' ≠ w j' := by
      intro i' j' hi' hj' he
      rw [hw_lt i' hi', hw_ge j' hj'] at he
      have hval : P.vertex (a + ((i'.val : ℕ) : ZMod (m + 3))) ∈
          ({P.vertex a, P.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
        rw [← hinter]
        exact ⟨hPedge i'.val hi' (left_mem_segment ℝ _ _),
          he ▸ hP'edge (j'.val - k) (by have := hbound j'; omega) (left_mem_segment ℝ _ _)⟩
      rcases hval with hval | hval
      · 
        have h0 : i'.val = 0 := by
          have := P.natCast_shift_inj a (show i'.val < m + 3 by omega) (show 0 < m + 3 by omega)
            (by rw [hval, Nat.cast_zero, add_zero])
          omega
        have hlast : P'.vertex (b + ((j'.val - k : ℕ) : ZMod (m' + 3)))
            = P'.vertex (b + ((l : ℕ) : ZMod (m' + 3))) := by rw [hend, ← he, hval]
        have := P'.natCast_shift_inj b (show j'.val - k < m' + 3 by have := hbound j'; omega)
          (show l < m' + 3 by omega) hlast
        have := hbound j'
        omega
      · have := P.natCast_shift_inj a (show i'.val < m + 3 by omega) (show k < m + 3 by omega)
          (by rw [hval])
        omega
    by_cases hli : i.val < k <;> by_cases hlj : j.val < k
    · rw [hw_lt i hli, hw_lt j hlj] at hij
      exact ZMod.val_injective _ (P.natCast_shift_inj a (by omega) (by omega) hij)
    · exact absurd hij (hcase i j hli hlj)
    · exact absurd hij.symm (hcase j i hlj hli)
    · rw [hw_ge i hli, hw_ge j hlj] at hij
      have := P'.natCast_shift_inj b (show i.val - k < m' + 3 by omega)
        (show j.val - k < m' + 3 by omega) hij
      exact ZMod.val_injective _ (by omega)
  · 
    intro i j hij
    have hib := hbound i
    have hjb := hbound j
    by_cases hli : i.val < k <;> by_cases hlj : j.val < k
    · rw [hE_lt i hli, hE_lt j hlj, hends_lt i hli]
      refine P.edges_meet _ _ fun he => hij (ZMod.val_injective _ ?_)
      exact P.natCast_shift_inj a (by omega) (by omega) (by rw [he])
    · rw [hE_lt i hli, hE_ge j hlj, hends_lt i hli]
      intro z hz
      have hz' := hcross i.val hli (j.val - k) (by omega) hz
      rcases hz' with rfl | rfl
      exacts [vertex_mem_edge_elim (P := P) (c := a) hz.1,
        vertex_mem_edge_elim (P := P) (c := a + (k : ZMod (m + 3))) hz.1]
    · rw [hE_ge i hli, hE_lt j hlj, hends_ge i hli]
      intro z hz
      have hz' := hcross j.val hlj (i.val - k) (by omega) ⟨hz.2, hz.1⟩
      rcases hz' with rfl | rfl
      · rw [← hend]
        exact vertex_mem_edge_elim (P := P') (c := b + (l : ZMod (m' + 3)))
          (by rw [hend]; exact hz.1)
      · rw [← hstart]
        exact vertex_mem_edge_elim (P := P') (c := b) (by rw [hstart]; exact hz.1)
    · rw [hE_ge i hli, hE_ge j hlj, hends_ge i hli]
      refine P'.edges_meet _ _ fun he => hij (ZMod.val_injective _ ?_)
      have := P'.natCast_shift_inj b (show i.val - k < m' + 3 by omega)
        (show j.val - k < m' + 3 by omega) (by rw [he])
      omega
  · 
    have hrange : List.range (n + 3) = List.range k ++ (List.range l).map (k + ·) := by
      rw [← hn]; exact List.range_add
    change ((List.range (n + 3)).map fun j : ℕ =>
        (w ((j : ℕ) : ZMod (n + 3)), w (((j : ℕ) : ZMod (n + 3)) + 1))) = _
    rw [hrange, List.map_append, List.map_map, arcPieces, arcPieces]
    congr 1
    · refine List.map_congr_left fun t ht => ?_
      have htk : t < k := List.mem_range.1 ht
      have hval : ((t : ZMod (n + 3))).val = t := ZMod.val_cast_of_lt (by omega)
      have h1 : ((t : ZMod (n + 3))).val < k := by rw [hval]; exact htk
      rw [hw_lt _ h1, hsucc_lt _ h1, hval]
    · refine List.map_congr_left fun s hs => ?_
      have hsl : s < l := List.mem_range.1 hs
      have hval : (((k + s : ℕ) : ZMod (n + 3))).val = k + s := ZMod.val_cast_of_lt (by omega)
      have h1 : ¬ (((k + s : ℕ) : ZMod (n + 3))).val < k := by rw [hval]; omega
      simp only [Function.comp_apply]
      rw [hw_ge _ h1, hsucc_ge _ h1, hval, show k + s - k = s by omega]

 





 
def reverse {m : ℕ} (P : PrePolygon m) : PrePolygon m where
  vertex j := P.vertex (-j)
  vertex_inj _ _ h := neg_injective (P.vertex_inj h)
  edges_meet i j hij := by
    have e1 : (-(i + 1) : ZMod (m + 3)) = -i - 1 := by ring
    have e2 : (-(j + 1) : ZMod (m + 3)) = -j - 1 := by ring
    have e3 : (-i - 1 : ZMod (m + 3)) + 1 = -i := by ring
    have e4 : (-j - 1 : ZMod (m + 3)) + 1 = -j := by ring
    have hij' : (-i - 1 : ZMod (m + 3)) ≠ -j - 1 := fun h => hij (by linear_combination -h)
    have h := P.edges_meet (-i - 1) (-j - 1) hij'
    rw [e3, e4] at h
    simp only [e1, e2]
    rw [segment_symm ℝ (P.vertex (-i)) (P.vertex (-i - 1)),
      segment_symm ℝ (P.vertex (-j)) (P.vertex (-j - 1)), Set.pair_comm]
    exact h

@[simp] theorem reverse_vertex {m : ℕ} (P : PrePolygon m) (j : ZMod (m + 3)) :
    P.reverse.vertex j = P.vertex (-j) := rfl

theorem reverse_edge {m : ℕ} (P : PrePolygon m) (j : ZMod (m + 3)) :
    P.reverse.edge j = P.edge (-j - 1) := by
  rw [edge, edge, reverse_vertex, reverse_vertex,
    show (-(j + 1) : ZMod (m + 3)) = -j - 1 by ring,
    show (-j - 1 : ZMod (m + 3)) + 1 = -j by ring]
  exact segment_symm ℝ _ _

@[simp] theorem reverse_carrier {m : ℕ} (P : PrePolygon m) : P.reverse.carrier = P.carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [reverse_edge] at hi
    exact Set.mem_iUnion.2 ⟨_, hi⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    refine Set.mem_iUnion.2 ⟨-i - 1, ?_⟩
    rw [reverse_edge, show (-(-i - 1) - 1 : ZMod (m + 3)) = i by ring]
    exact hi

 
theorem reverse_arc {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.reverse.arc (-a - (k : ZMod (m + 3))) k = P.arc a k := by
  ext z
  rw [mem_arc_iff, mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    rw [reverse_edge] at hz
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [show a + ((k - t - 1 : ℕ) : ZMod (m + 3))
        = -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3))) - 1 by
      linear_combination ClosedPolygon.reverse_natCast (n := m + 3) ht]
    exact hz
  · rintro ⟨t, ht, hz⟩
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [reverse_edge, show -(-a - (k : ZMod (m + 3)) + ((k - t - 1 : ℕ) : ZMod (m + 3))) - 1
        = a + (t : ZMod (m + 3)) by
      linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) ht]
    exact hz

 

theorem sameEdges_reverse_arcPieces {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    SameEdges (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k) (P.arcPieces a k) := by
  have key : (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k).map orientPiece
      = ((P.arcPieces a k).map orientPiece).reverse := by
    rw [arcPieces, arcPieces, List.map_map, List.map_map, ← List.map_reverse,
      List.range_eq_range', List.reverse_range', ← List.range_eq_range', List.map_map]
    refine List.map_congr_left fun t ht => ?_
    have htk : t < k := List.mem_range.1 ht
    have he : (0 + k - 1 - t : ℕ) = k - t - 1 := by omega
    simp only [Function.comp_apply, he, reverse_vertex]
    rw [show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)))
          = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) + 1 by
        linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) htk,
      show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)) + 1)
        = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) by
        linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) htk]
    exact orientPiece_swap (_, _)
  rw [SameEdges, key]
  exact List.reverse_perm _

end PrePolygon

 






 
theorem exists_prePolygon_arcs {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      ((P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂) ∨
        (P.arc a k = A₂ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₁)) := by
  obtain ⟨m, P, a, k, hcar, hpa, hqa, hk1, hk2⟩ := exists_prePolygon_split hJ hP hp hq hpq
  refine ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, ?_⟩
  have hD1 : IsArcBetween (P.arc a k) p q := by
    rw [← hpa, ← hqa]; exact P.isArcBetween_arc a hk1 hk2
  have hD2 : IsArcBetween (P.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    have h := P.isArcBetween_arc (a + (k : ZMod (m + 3))) (k := m + 3 - k) (by omega) (by omega)
    rw [zmod_add_sub_cancel (by omega) a] at h
    rw [← hpa, ← hqa]
    exact h.reverse
  have hDunion : P.arc a k ∪ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = C := by
    rw [P.arc_union a (by omega), hcar]
  have hDinter : P.arc a k ∩ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [P.arc_inter a hk1 hk2, hpa, hqa]
  rcases two_arcs_unique hunion hinter hDunion hDinter hA1 hA2 hD1 hD2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨e1.symm, e2.symm⟩
  · exact Or.inr ⟨e2.symm, e1.symm⟩

 






theorem exists_prePolygon_arcs_oriented {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂ := by
  obtain ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, hcase⟩ :=
    exists_prePolygon_arcs hJ hP hp hq hpq hA1 hA2 hunion hinter
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, e1, e2⟩
  · 
    have hneg : ((m + 3 - k : ℕ) : ZMod (m + 3)) = -(k : ZMod (m + 3)) := by
      linear_combination zmod_add_sub_cancel (m := m) (k := k) (by omega) 0
    refine ⟨m, P.reverse, -a, m + 3 - k, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [PrePolygon.reverse_carrier]; exact hcar
    · rw [PrePolygon.reverse_vertex, neg_neg]; exact hpa
    · rw [PrePolygon.reverse_vertex, hneg,
        show -(-a + -(k : ZMod (m + 3))) = a + (k : ZMod (m + 3)) by ring]
      exact hqa
    · have h := P.reverse_arc (a + (k : ZMod (m + 3))) (m + 3 - k)
      rw [hneg, show -(a + (k : ZMod (m + 3))) - -(k : ZMod (m + 3)) = -a by ring] at h
      rw [h]; exact e2
    · have h := P.reverse_arc a k
      rw [show m + 3 - (m + 3 - k) = k by omega, hneg,
        show -a + -(k : ZMod (m + 3)) = -a - (k : ZMod (m + 3)) by ring, h]
      exact e1

 








variable {m m₁ m₂ : ℕ} {C : PrePolygon m} {J₁ : PrePolygon m₁} {J₂ : PrePolygon m₂}
  {K : List Piece} {a : ZMod (m + 3)} {k : ℕ} {y : Plane}

 

structure IsPrePolygonalCrosscut (C : PrePolygon m) (J₁ : PrePolygon m₁) (J₂ : PrePolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (y : Plane) : Prop where
   
  le : k ≤ m + 3
   
  edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K)
   
  edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K)
   
  meets₁ : cover K ∩ C.carrier ⊆ C.arc a k
   
  meets₂ : cover K ∩ C.carrier ⊆ C.arc (a + k) (m + 3 - k)
   
  notMem : y ∉ C.carrier
   
  avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)

 

theorem IsPrePolygonalCrosscut.of_endpoints (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    (meets : cover K ∩ C.carrier ⊆ ({C.vertex a, C.vertex (a + k)} : Set Plane))
    (notMem : y ∉ C.carrier)
    (avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)) :
    IsPrePolygonalCrosscut C J₁ J₂ K a k y :=
  ⟨by omega, edges₁, edges₂, meets.trans (C.endpoints_subset_arc a hk1),
    meets.trans (C.endpoints_subset_arc' a hk2), notMem, avoids⟩

namespace IsPrePolygonalCrosscut

variable (h : IsPrePolygonalCrosscut C J₁ J₂ K a k y)
include h

 
theorem symm : IsPrePolygonalCrosscut C J₂ J₁ K (a + k) (m + 3 - k) y := by
  have hk : k ≤ m + 3 := h.le
  have hnat : m + 3 - (m + 3 - k) = k := by omega
  have hzmod := zmod_add_sub_cancel (k := k) hk a
  refine ⟨by omega, h.edges₂, ?_, h.meets₂, ?_, h.notMem, h.avoids⟩
  · rw [hzmod, hnat]; exact h.edges₁
  · rw [hzmod, hnat]; exact h.meets₁

 

theorem notMem_cover : y ∉ cover K :=
  fun hy => Set.disjoint_left.1 h.avoids hy (mem_connectedComponentIn h.notMem)

theorem carrier₁ : J₁.carrier = C.arc a k ∪ cover K :=
  PrePolygon.carrier_eq_of_sameEdges h.edges₁

theorem notMem_carrier₁ : y ∉ J₁.carrier :=
  PrePolygon.notMem_carrier_of_sameEdges h.edges₁ h.notMem h.notMem_cover

theorem cover_subset_carrier₁ : cover K ⊆ J₁.carrier := by
  rw [h.carrier₁]; exact Set.subset_union_right

theorem carrier₁_subset : J₁.carrier ⊆ C.carrier ∪ cover K := by
  rw [h.carrier₁]
  exact Set.union_subset_union_left _ (C.arc_subset_carrier a k)

 
theorem nondeg : ∀ Q ∈ K, Q.Nondeg := by
  intro Q hQ
  obtain ⟨R, hR, hRQ⟩ := h.edges₁.symm.exists_mem (List.mem_append_right _ hQ)
  have hRn : (orientPiece R).Nondeg := orientPiece_nondeg (J₁.pieces_nondeg R hR)
  rw [hRQ] at hRn
  rcases orientPiece_eq_or Q with e | e
  · rw [e] at hRn; exact hRn
  · rw [e] at hRn; exact fun hh => hRn hh.symm

 
theorem exists_direction : ∃ u : Plane, Plane.IsDirection u ∧
    (∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) ∧ (∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) := by
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ K) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with hQ' | hQ'
    · exact C.pieces_nondeg Q hQ'
    · exact h.nondeg Q hQ')
  exact ⟨u, hu, fun Q hQ => hlev Q (List.mem_append_left _ hQ),
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)⟩

 

theorem regionPairC :
    IsRegionPair C.carrier (farRegion C.carrier y) (connectedComponentIn C.carrierᶜ y) :=
  (C.isSeparating_carrier.isRegionPair_farRegion h.notMem).symm

theorem regionPair₁ :
    IsRegionPair J₁.carrier (connectedComponentIn J₁.carrierᶜ y) (farRegion J₁.carrier y) :=
  J₁.isSeparating_carrier.isRegionPair_farRegion h.notMem_carrier₁

 
theorem near_subset₁ :
    connectedComponentIn C.carrierᶜ y ⊆ connectedComponentIn J₁.carrierᶜ y := by
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_connectedComponentIn h.notMem) (fun w hw => ?_)
  have hwC : w ∉ C.carrier := connectedComponentIn_subset _ _ hw
  have hwK : w ∉ cover K := fun hK => Set.disjoint_left.1 h.avoids hK hw
  exact PrePolygon.notMem_carrier_of_sameEdges h.edges₁ hwC hwK

 
theorem cell_subset₁ : farRegion J₁.carrier y ⊆ farRegion C.carrier y \ cover K :=
  cell_subset_region_diff (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁

theorem cell_subset₂ : farRegion J₂.carrier y ⊆ farRegion C.carrier y \ cover K :=
  h.symm.cell_subset₁

 
theorem cell_isComponent₁ : ∀ z ∈ farRegion J₁.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₁.carrier y :=
  cell_isComponent (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁ h.carrier₁_subset

theorem cell_isComponent₂ : ∀ z ∈ farRegion J₂.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₂.carrier y :=
  h.symm.cell_isComponent₁

 
theorem closure_cell_inter₁ : closure (farRegion J₁.carrier y) ∩ C.carrier = C.arc a k := by
  rw [closure_cell_inter_curve C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC.right h.regionPair₁ h.near_subset₁, h.carrier₁]
  refine Set.Subset.antisymm ?_ (fun w hw => ⟨Or.inl hw, C.arc_subset_carrier a k hw⟩)
  rintro w ⟨hw | hw, hwC⟩
  · exact hw
  · exact h.meets₁ ⟨hw, hwC⟩

theorem closure_cell_inter₂ :
    closure (farRegion J₂.carrier y) ∩ C.carrier = C.arc (a + k) (m + 3 - k) :=
  h.symm.closure_cell_inter₁

 

 

theorem separates_xor {x : Plane} (hxC : x ∉ C.carrier) (hxK : x ∉ cover K) :
    x ∈ farRegion C.carrier y ↔
      (x ∈ farRegion J₁.carrier y ↔ ¬ x ∈ farRegion J₂.carrier y) := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  have hlev₁ := h.edges₁.hgt_ne (PrePolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hlev₂ := h.edges₂.hgt_ne (PrePolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hxJ₁ := PrePolygon.notMem_carrier_of_sameEdges h.edges₁ hxC hxK
  have hxJ₂ := PrePolygon.notMem_carrier_of_sameEdges h.edges₂ hxC hxK
  rw [← C.parity_ne_iff_mem_farRegion hu hlevC hxC h.notMem,
    ← J₁.parity_ne_iff_mem_farRegion hu hlev₁ hxJ₁ h.notMem_carrier₁,
    ← J₂.parity_ne_iff_mem_farRegion hu hlev₂ hxJ₂ h.symm.notMem_carrier₁]
  have hsx := C.parity_splitting u a h.le h.edges₁ h.edges₂ x
  have hsy := C.parity_splitting u a h.le h.edges₁ h.edges₂ y
  have key : ∀ s₁ s₂ s t₁ t₂ t : ZMod 2, s₁ + s₂ = s → t₁ + t₂ = t →
      (s ≠ t ↔ ((s₁ ≠ t₁) ↔ ¬ (s₂ ≠ t₂))) := by decide
  exact key _ _ _ _ _ _ hsx hsy

 
theorem region_eq :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  refine Set.Subset.antisymm ?_ (Set.union_subset h.cell_subset₁ h.cell_subset₂)
  rintro w ⟨hwΩ, hwK⟩
  by_cases hw₁ : w ∈ farRegion J₁.carrier y
  · exact Or.inl hw₁
  · refine Or.inr ?_
    by_contra hw₂
    exact hw₁ (((h.separates_xor hwΩ.1 hwK).1 hwΩ).2 hw₂)

 

 
theorem connectedComponentIn_cover_eq {z : Plane} (hz : z ∈ cover K) (hzC : z ∉ C.carrier) :
    connectedComponentIn C.carrierᶜ z = farRegion C.carrier y :=
  h.regionPairC.left.connectedComponentIn_eq C.isSeparating_carrier
    (diff_subset_farRegion h.avoids ⟨hz, hzC⟩)

 
theorem inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hconn : IsPreconnected Q) (hside : Q ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ closure Q) (hw₂ : w₂ ∈ closure Q)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
  have hsub : Q ⊆ farRegion C.carrier y \ cover K :=
    fun z hz => ⟨hside hz, fun hzK => hempty z ⟨hz, hzK⟩⟩
  obtain ⟨z, hz⟩ : Q.Nonempty := by
    by_contra hQ
    rw [Set.not_nonempty_iff_eq_empty] at hQ
    rw [hQ, closure_empty] at hw₁
    simp at hw₁
  have hzcell : z ∈ farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
    rw [← h.region_eq]; exact hsub hz
  rcases hzcell with hz₁ | hz₂
  · have hQ₁ : Q ⊆ farRegion J₁.carrier y := by
      have hcc := hconn.subset_connectedComponentIn hz hsub
      rwa [h.cell_isComponent₁ z hz₁] at hcc
    have hmem : w₂ ∈ closure (farRegion J₁.carrier y) ∩ C.carrier :=
      ⟨closure_mono hQ₁ hw₂, C.arc_subset_carrier _ _ hw₂B⟩
    rw [h.closure_cell_inter₁] at hmem
    exact hw₂A hmem
  · have hQ₂ : Q ⊆ farRegion J₂.carrier y := by
      have hcc := hconn.subset_connectedComponentIn hz hsub
      rwa [h.cell_isComponent₂ z hz₂] at hcc
    have hmem : w₁ ∈ closure (farRegion J₂.carrier y) ∩ C.carrier :=
      ⟨closure_mono hQ₂ hw₁, C.arc_subset_carrier _ _ hw₁A⟩
    rw [h.closure_cell_inter₂] at hmem
    exact hw₁B hmem

 
theorem arc_inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hQ : IsArcBetween Q w₁ w₂) (hside : Q \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  obtain ⟨z, hzQ, hzK⟩ := h.inter_cover_nonempty hQ.isPreconnected_diff hside
    hQ.left_mem_closure_diff hQ.right_mem_closure_diff hw₁A hw₁B hw₂B hw₂A
  exact ⟨z, hzQ.1, hzK⟩

 
theorem alternating_inter_nonempty {A B Q : Set Plane} {p q w₁ w₂ : Plane}
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hQ : IsArcBetween Q w₁ w₂) (hside : Q \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (Q ∩ cover K).Nonempty := by
  refine h.arc_inter_cover_nonempty hQ hside (hA ▸ hw₁.1) ?_ (hB ▸ hw₂.1) ?_
  · rw [hB]; exact fun hmem => hw₁.2 (hAB ▸ Set.mem_inter hw₁.1 hmem)
  · rw [hA]; exact fun hmem => hw₂.2 (hAB ▸ Set.mem_inter hmem hw₂.1)

 
theorem alternating_inter_nonempty_of_same_side {A B Q : Set Plane} {p q w₁ w₂ z : Plane}
    (hz : z ∈ cover K) (hzC : z ∉ C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hQ : IsArcBetween Q w₁ w₂)
    (hside : Q \ {w₁, w₂} ⊆ connectedComponentIn C.carrierᶜ z)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (Q ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hQ
    (hside.trans (h.connectedComponentIn_cover_eq hz hzC).subset) hw₁ hw₂

end IsPrePolygonalCrosscut

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s : Fin 3} {R : Set Plane}

 





 

def IsPreHexCrosscut (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : PrePolygon m) (J₁ : PrePolygon m₁) (J₂ : PrePolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (yref : Plane),
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      IsPrePolygonalCrosscut C J₁ J₂ K a k yref

namespace IsK33Config

 





theorem isPreHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPreHexCrosscut drawing e s := by
  have hpq : x s ≠ y (s + 1) := h.x_ne_y s (s + 1)
  have hA1 := h.arcA_isArcBetween hd s
  have hA2 := h.arcB_isArcBetween hd s
  have hCh := hd.edge_isArcBetween (h.isLink s (s + 1))
  have hinterA := h.chord_inter_arcA hd s
  have hinterB := h.chord_inter_arcB hd s
  have hPch : IsPolygonal (edgeArc drawing (e s (s + 1))) :=
    hpoly _ (h.isLink s (s + 1)).edge_mem
  have hP1 : IsPolygonal (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    (h.isPolygonal_arcA hd hpoly s).union hPch ⟨x s, hA1.left_mem, hCh.left_mem⟩
  have hJ1 : IsJordanCurve (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    IsJordanCurve.of_two_arcs hA1 hCh.reverse fun z hz1 hz2 => by
      have hz : z ∈ ({x s, y (s + 1)} : Set Plane) := hinterA ▸ ⟨hz1, hz2⟩
      simpa using hz
  
  obtain ⟨m, C, a, k, hCcar, hk1, hk2, hCa, hCak, hCarc1, hCarc2⟩ :=
    exists_prePolygon_arcs_oriented (h.hexagon_isJordanCurve hd) (h.isPolygonal_hexSet hd hpoly)
      (h.x_mem_hexSet hd s) (h.y_mem_hexSet hd (s + 1)) hpq hA1 hA2
      (arcs_union (drawing := drawing) (e := e) s) (h.arcs_inter hd s)
  
  obtain ⟨m₁, D, b, l, -, hl1, hl2, hDb, hDbl, hDarc1, hDarc2⟩ :=
    exists_prePolygon_arcs_oriented hJ1 hP1 (Or.inl hA1.left_mem) (Or.inl hA1.right_mem) hpq
      hA1 hCh rfl hinterA
  set c : ZMod (m₁ + 3) := b + (l : ZMod (m₁ + 3)) with hc
  set r : ℕ := m₁ + 3 - l with hr
  have hwrapD : c + (r : ZMod (m₁ + 3)) = b := zmod_add_sub_cancel (by omega) b
  have hDc : D.vertex c = y (s + 1) := hDbl
  have hDcr : D.vertex (c + (r : ZMod (m₁ + 3))) = x s := by rw [hwrapD]; exact hDb
  have hKcover : cover (D.arcPieces c r) = edgeArc drawing (e s (s + 1)) := hDarc2
  have hKinter : C.arc a k ∩ D.arc c r
      = ({C.vertex a, C.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
    rw [hCarc1, hDarc2, hCa, hCak]; exact hinterA
  
  obtain ⟨n₁, J₁, hJ₁p⟩ := PrePolygon.exists_splice C D hk1 hk2 (by omega) (by omega)
    (by rw [hDc, hCak]) (by rw [hDcr, hCa]) hKinter
  
  have hwrapC : a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a :=
    zmod_add_sub_cancel (by omega) a
  set c' : ZMod (m₁ + 3) := -c - (r : ZMod (m₁ + 3)) with hc'
  have hDrev1 : D.reverse.vertex c' = x s := by
    rw [PrePolygon.reverse_vertex, hc', show -(-c - (r : ZMod (m₁ + 3))) = c + (r : ZMod (m₁ + 3))
      by ring]
    exact hDcr
  have hDrev2 : D.reverse.vertex (c' + (r : ZMod (m₁ + 3))) = y (s + 1) := by
    rw [PrePolygon.reverse_vertex, hc',
      show -(-c - (r : ZMod (m₁ + 3)) + (r : ZMod (m₁ + 3))) = c by ring]
    exact hDc
  have hKinter' : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∩ D.reverse.arc c' r
      = ({C.vertex (a + (k : ZMod (m + 3))),
          C.vertex (a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)))} : Set Plane) := by
    rw [hCarc2, hc', D.reverse_arc c r, hDarc2, hwrapC, hCa, hCak, Set.pair_comm]
    exact hinterB
  obtain ⟨n₂, J₂, hJ₂p⟩ := PrePolygon.exists_splice C D.reverse (a := a + (k : ZMod (m + 3)))
    (k := m + 3 - k) (b := c') (l := r) (by omega) (by omega) (by omega) (by omega)
    (by rw [hDrev1, hwrapC, hCa]) (by rw [hDrev2, hCak]) hKinter'
  
  have hsep : IsSeparating (hexSet drawing e) := hCcar ▸ C.isSeparating_carrier
  obtain ⟨yref, hyref, hdisj⟩ := h.exists_reference_point hd hsep s
  refine ⟨m, n₁, n₂, C, J₁, J₂, D.arcPieces c r, a, k, yref, hCcar, hCarc1, hCarc2, hKcover,
    ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hJ₁p]
  · rw [hJ₂p]
    exact SameEdges.append (SameEdges.refl _) (D.sameEdges_reverse_arcPieces c r)
  · rw [hKcover, hCcar, hCarc1, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcA hd s
  · rw [hKcover, hCcar, hCarc2, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcB hd s
  · rw [hCcar]; exact hyref
  · rw [hKcover, hCcar]; exact hdisj

 

 


theorem false_of_isPreHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : IsPreHexCrosscut drawing e s) (hsep : IsSeparating (hexSet drawing e))
    (hR : IsRegionOf (hexSet drawing e) R)
    (h1 : openArc (drawing (e s (s + 1))) ⊆ R)
    (h2 : openArc (drawing (e (s + 1) (s + 1 + 1))) ⊆ R) : False := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK, hcc⟩ := hcross
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzK : z ∈ cover K := by rw [hK]; exact h.chord_openArc_subset_edgeArc hd s hz
  have hzC : z ∉ C.carrier := by rw [hcar]; exact h.chord_openArc_subset_compl hd s hz
  have hzR : z ∈ R := h1 hz
  have hside : edgeArc drawing (e (s + 1) (s + 1 + 1)) \ ({x (s + 1), y (s + 1 + 1)} : Set Plane)
      ⊆ connectedComponentIn C.carrierᶜ z := by
    rw [hcar, hR.connectedComponentIn_eq hsep hzR, ← h.chord_openArc_eq hd (s + 1)]
    exact h2
  obtain ⟨w, hw₁, hw₂⟩ := hcc.alternating_inter_nonempty_of_same_side hzK hzC hA hB
    (h.arcs_inter hd s) (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1 + 1))) hside
    (h.x_succ_mem_arcA hd s) (h.y_succ_mem_arcB hd s)
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  have hdis := h.chords_disjoint hd (hs1 s)
  rw [Set.eq_empty_iff_forall_notMem] at hdis
  exact hdis w ⟨hw₁, by rwa [hK] at hw₂⟩

 
theorem false_of_polygonal (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) : False := by
  have hsep : IsSeparating (hexSet drawing e) := by
    obtain ⟨_, _, _, C, _, _, _, _, _, _, hcar, _⟩ := h.isPreHexCrosscut hd hpoly 0
    exact hcar ▸ C.isSeparating_carrier
  obtain ⟨s, t, hst, R, hR, h1, h2⟩ := h.exists_two_chords_same_region hd hsep
  have hpair : ∀ s t : Fin 3, s ≠ t → t = s + 1 ∨ s = t + 1 := by decide
  rcases hpair s t hst with rfl | rfl
  · exact h.false_of_isPreHexCrosscut hd (h.isPreHexCrosscut hd hpoly s) hsep hR h1 h2
  · exact h.false_of_isPreHexCrosscut hd (h.isPreHexCrosscut hd hpoly t) hsep hR h2 h1

 








theorem not_exists_isDrawing [G.Finite] (h : IsK33Config G x y e) :
    ¬ ∃ dr : β → ℝ → Plane, IsDrawing G dr := by
  rintro ⟨dr, hdr⟩
  obtain ⟨dr', hdr', hpoly'⟩ := polygonal_redrawing G dr hdr
  exact h.false_of_polygonal hdr' hpoly'

end IsK33Config

 

theorem IsArcK33.elim {P : Fin 3 → Fin 3 → Set Plane} (h : IsArcK33 x y P) : False :=
  h.isK33Config.not_exists_isDrawing ⟨h.arcDrawing, h.isDrawing⟩

 

theorem IsK33Subdivision.elim {H : Graph Plane β} {W : Fin 3 → Fin 3 → List β}
    (hd : IsDrawing H drawing) (h : IsK33Subdivision H x y W) : False :=
  (h.isArcK33 hd).elim

 


theorem k33Graph_not_exists_isDrawing (x y : Fin 3 → Plane) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) :
    ¬ ∃ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr :=
  IsK33Config.not_exists_isDrawing ⟨k33Graph_isLink x y, hx, hy, hxy⟩

end Graph
