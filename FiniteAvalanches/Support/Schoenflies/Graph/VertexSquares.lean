/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/VertexSquares.lean.
-/
import FiniteAvalanches.Support.Schoenflies.Square
import FiniteAvalanches.Support.Schoenflies.UniformBound
import FiniteAvalanches.Support.Schoenflies.Subarc
import FiniteAvalanches.Support.Schoenflies.Graph.Drawing

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 














































open Metric Set unitInterval

namespace Schoenflies

namespace Plane

 





 

theorem closedSquare_mono_center (c : Plane) {r s : ℝ} (h : r ≤ s) :
    closedSquare c r ⊆ closedSquare c s := fun _ hx => le_trans hx h

 
theorem mem_closedSquare_self (c : Plane) {r : ℝ} (hr : 0 ≤ r) : c ∈ closedSquare c r := by
  change supDist c c ≤ r
  rw [supDist_self]; exact hr

theorem supDist_eq_dist_le (x c : Plane) : supDist x c ≤ dist x c := by
  rw [dist_eq_norm]; exact supNorm_le_norm _

 

theorem closedBall_subset_closedSquare (c : Plane) (r : ℝ) :
    closedBall c r ⊆ closedSquare c r := fun _ hx =>
  le_trans (supDist_eq_dist_le _ _) (mem_closedBall.1 hx)

 

theorem closedSquare_subset_ball {c : Plane} {ρ : ℝ} (hρ : 0 < ρ) :
    closedSquare c (ρ / 2) ⊆ ball c ρ := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x c ≤ ρ / 2 := hx
  have hnorm : ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) :=
    le_trans (norm_le_sqrt_two_mul_supNorm _)
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))
  rw [mem_ball, dist_eq_norm]
  calc ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) := hnorm
    _ < 2 * (ρ / 2) := by
        exact mul_lt_mul_of_pos_right hsqrt (by linarith)
    _ = ρ := by ring

end Plane

 

 





theorem isCompact_parameters_mem {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) : IsCompact {t | t ∈ Icc α β ∧ f t ∈ C} := by
  have hset : {t | t ∈ Icc α β ∧ f t ∈ C} = Icc α β ∩ f ⁻¹' C := rfl
  rw [hset]
  exact isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc hC) inter_subset_left

 




theorem exists_last_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, s < t → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sSup S ∈ S := hcpt.sSup_mem hne
  refine ⟨sSup S, hsI, le_csSup hcpt.bddAbove ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  
  exact absurd (le_csSup hcpt.bddAbove ⟨htI, htC⟩) (not_le.2 hlt)

 

theorem exists_first_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, s ≤ t₀ ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, t < s → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sInf S ∈ S := hcpt.sInf_mem hne
  refine ⟨sInf S, hsI, csInf_le hcpt.bddBelow ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  exact absurd (csInf_le hcpt.bddBelow ⟨htI, htC⟩) (not_le.2 hlt)

 
theorem exists_last_mem {f : ℝ → Plane} (hf : ContinuousOn f I) {C : Set Plane}
    (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hmem : f t₀ ∈ C) :
    ∃ s ∈ I, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ I, s < t → f t ∉ C :=
  exists_last_mem_Icc hf hC ht₀ hmem

 

theorem exists_first_mem {f : ℝ → Plane} (hf : ContinuousOn f I) {C : Set Plane}
    (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hmem : f t₀ ∈ C) :
    ∃ s ∈ I, s ≤ t₀ ∧ f s ∈ C ∧ ∀ t ∈ I, t < s → f t ∉ C :=
  exists_first_mem_Icc hf hC ht₀ hmem

end Schoenflies

 

open Schoenflies
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

 

theorem IsDrawing.notMem_edgeArc_of_not_inc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G))
    {v : Plane} (hv : v ∈ V(G)) (hinc : ¬ G.Inc e v) : v ∉ edgeArc drawing e := by
  intro hmem
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  rcases h.vertex_mem_edgeArc hxy hv hmem with rfl | rfl
  · exact hinc hxy.inc_left
  · exact hinc hxy.inc_right

 





theorem IsDrawing.exists_square_at [G.Finite] (h : IsDrawing G drawing) {v : Plane}
    (hv : v ∈ V(G)) :
    ∃ r > 0, (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      ∀ e ∈ E(G), ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
  
  obtain ⟨r₁, hr₁, hvert⟩ :
      ∃ r > 0, ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun w r => w ≠ v → w ∉ Plane.closedSquare v r) ?_ ?_
    · exact fun w δ ε _ hδε hP hne hmem =>
        hP hne (Plane.closedSquare_mono_center v hδε hmem)
    · intro w hw
      by_cases hwv : w = v
      · exact ⟨1, one_pos, fun hne => absurd hwv hne⟩
      · 
        
        have hpos : 0 < dist w v := dist_pos.2 hwv
        refine ⟨dist w v / 2, by linarith, fun _ hmem => ?_⟩
        exact absurd (mem_ball.1 (Plane.closedSquare_subset_ball hpos hmem)) (by simp)
  
  obtain ⟨r₂, hr₂, hedge⟩ :
      ∃ r > 0, ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun e r => ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e))
      ?_ ?_
    · exact fun e δ ε _ hδε hP hinc =>
        Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hP hinc)
    · intro e he
      by_cases hinc : G.Inc e v
      · exact ⟨1, one_pos, fun h' => absurd hinc h'⟩
      · have hdisj : Disjoint ({v} : Set Plane) (edgeArc drawing e) :=
          Set.disjoint_singleton_left.2 (h.notMem_edgeArc_of_not_inc he hv hinc)
        obtain ⟨ρ, hρ, hsep⟩ :=
          Plane.exists_dist_pos isCompact_singleton (h.isCompact_edgeArc he) hdisj
        refine ⟨ρ / 2, by linarith, fun _ => Set.disjoint_left.2 fun x hx hxe => ?_⟩
        have hclose : dist x v < ρ := mem_ball.1 (Plane.closedSquare_subset_ball hρ hx)
        have hfar : ρ ≤ dist v x := hsep v rfl x hxe
        rw [dist_comm] at hfar
        linarith
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun w hw hne hmem => ?_, fun e he hinc => ?_⟩
  · exact hvert w hw hne (Plane.closedSquare_mono_center v (min_le_left _ _) hmem)
  · exact Set.disjoint_of_subset_left
      (Plane.closedSquare_mono_center v (min_le_right _ _)) (hedge e he hinc)

 







theorem IsDrawing.exists_vertexSquares [G.Finite] (h : IsDrawing G drawing) :
    ∃ r > 0,
      (∀ v ∈ V(G), ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      (∀ v ∈ V(G), ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ∧
      ∀ v ∈ V(G), ∀ w ∈ V(G), v ≠ w →
        Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r) := by
  
  obtain ⟨r, hr, hall⟩ :
      ∃ r > 0, ∀ v ∈ V(G),
        (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun v r => (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ?_ ?_
    · rintro v δ ε _ hδε ⟨hP, hQ⟩
      exact ⟨fun w hw hne hmem => hP w hw hne (Plane.closedSquare_mono_center v hδε hmem),
        fun e he hinc =>
          Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hQ e he hinc)⟩
    · exact fun v hv => h.exists_square_at hv
  refine ⟨r / 2, by linarith, fun v hv w hw hne hmem => ?_, fun v hv e he hinc => ?_,
    fun v hv w hw hne => Set.disjoint_left.2 fun x hxv hxw => ?_⟩
  · exact (hall v hv).1 w hw hne (Plane.closedSquare_mono_center v (by linarith) hmem)
  · exact Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v (by linarith))
      ((hall v hv).2 e he hinc)
  · 
    have hvx : Plane.supDist x v ≤ r / 2 := hxv
    have hwx : Plane.supDist x w ≤ r / 2 := hxw
    have : Plane.supDist w v ≤ r := by
      have := Plane.supDist_triangle w x v
      rw [Plane.supDist_comm w x] at this
      linarith
    exact (hall v hv).1 w hw (Ne.symm hne) this

 

 
theorem not_inc_of_ne {e : β} {v w u : Plane} (hlink : G.IsLink e v w) (huv : u ≠ v)
    (huw : u ≠ w) : ¬ G.Inc e u := fun hinc => (hinc.eq_or_eq_of_isLink hlink).elim huv huw

 


theorem IsDrawing.closedSquare_disjoint_edgeArc_of_ne {e : β} {v w u : Plane} {r : ℝ}
    (hsq : ∀ e ∈ E(G), ¬ G.Inc e u → Disjoint (Plane.closedSquare u r) (edgeArc drawing e))
    (hlink : G.IsLink e v w) (huv : u ≠ v) (huw : u ≠ w) :
    Disjoint (Plane.closedSquare u r) (edgeArc drawing e) :=
  hsq e hlink.edge_mem (not_inc_of_ne hlink huv huw)

 



theorem IsDrawing.disjoint_of_subset_edgeArc (h : IsDrawing G drawing) {e f : β}
    (he : e ∈ E(G)) (hf : f ∈ E(G)) (hef : e ≠ f) {K L : Set Plane}
    (hK : K ⊆ edgeArc drawing e) (hKV : Disjoint K V(G)) (hL : L ⊆ edgeArc drawing f) :
    Disjoint K L :=
  Set.disjoint_left.2 fun _ hxK hxL =>
    Set.disjoint_left.1 hKV hxK (h.arcs_meet_at_vertex he hf hef (hK hxK) (hL hxL))

 
















theorem IsDrawing.exists_core (h : IsDrawing G drawing) {e : β} {v w : Plane} {r : ℝ}
    (hr : 0 < r) (hlink : G.IsLink e v w)
    (hdisj : Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r)) :
    ∃ (K : Set Plane) (p q : Plane),
      K ⊆ edgeArc drawing e ∧ IsCompact K ∧ IsArcBetween K p q ∧
      K ∩ Plane.closedSquare v r = {p} ∧ K ∩ Plane.closedSquare w r = {q} ∧
      Disjoint K V(G) := by
  obtain ⟨f, hcont, hinj, himg, hf0, hf1⟩ := h.edge_isArcBetween hlink
  have hv0 : f 0 ∈ Plane.closedSquare v r := by
    rw [hf0]; exact Plane.mem_closedSquare_self v hr.le
  have hw1 : f 1 ∈ Plane.closedSquare w r := by
    rw [hf1]; exact Plane.mem_closedSquare_self w hr.le
  
  obtain ⟨a, haI, -, haD, hafter⟩ :=
    exists_last_mem hcont (Plane.isClosed_closedSquare v r) zero_mem_I hv0
  have hsub : Icc a 1 ⊆ I := fun t ht => ⟨le_trans haI.1 ht.1, ht.2⟩
  
  obtain ⟨b, hbmem, -, hbD, hbefore⟩ :=
    exists_first_mem_Icc (hcont.mono hsub) (Plane.isClosed_closedSquare w r)
      (right_mem_Icc.2 haI.2) hw1
  have hbI : b ∈ I := hsub hbmem
  have hne : a ≠ b := by
    intro hEq
    rw [hEq] at haD
    exact Set.disjoint_left.1 hdisj haD hbD
  have hIccI : Icc a b ⊆ I := fun t ht => ⟨le_trans haI.1 ht.1, le_trans ht.2 hbmem.2⟩
  
  have hpv : f a ≠ v := by
    intro hEq
    have ha0 : a = 0 := hinj haI zero_mem_I (by rw [hEq, hf0])
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hcont 0 zero_mem_I) r hr
    have ht0 : 0 < min (δ / 2) 1 := lt_min (by linarith) one_pos
    have htI : min (δ / 2) 1 ∈ I := ⟨ht0.le, min_le_right _ _⟩
    have hdist : dist (min (δ / 2) 1) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine hafter _ htI (by rw [ha0]; exact ht0) (Plane.closedBall_subset_closedSquare v r ?_)
    rw [mem_closedBall, ← hf0]
    exact (hclose htI hdist).le
  
  have hqw : f b ≠ w := by
    intro hEq
    have hb1 : b = 1 := hinj hbI one_mem_I (by rw [hEq, hf1])
    have halt1 : a < 1 := by rw [← hb1]; exact lt_of_le_of_ne hbmem.1 hne
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hcont 1 one_mem_I) r hr
    have hmax1 : max (1 - δ / 2) ((a + 1) / 2) < 1 := max_lt (by linarith) (by linarith)
    have hmaxa : a ≤ max (1 - δ / 2) ((a + 1) / 2) :=
      le_trans (by linarith) (le_max_right _ _)
    have htmem : max (1 - δ / 2) ((a + 1) / 2) ∈ Icc a 1 := ⟨hmaxa, hmax1.le⟩
    have hdist : dist (max (1 - δ / 2) ((a + 1) / 2)) 1 < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub]
      have := le_max_left (1 - δ / 2) ((a + 1) / 2)
      linarith
    refine hbefore _ htmem (by rw [hb1]; exact hmax1)
      (Plane.closedBall_subset_closedSquare w r ?_)
    rw [mem_closedBall, ← hf1]
    exact (hclose (hsub htmem) hdist).le
  
  have harc : IsArcBetween (f '' Icc a b) (f a) (f b) := by
    have hsubarc := isArcBetween_subarc_of_injOn_I hcont hinj haI hbI hne
    rwa [uIcc_of_le hbmem.1] at hsubarc
  have hKsub : f '' Icc a b ⊆ edgeArc drawing e := by
    rw [← himg]; exact image_mono hIccI
  have hKv : f '' Icc a b ∩ Plane.closedSquare v r = {f a} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxD⟩
      rcases eq_or_lt_of_le ht.1 with heq | hlt
      · simp [heq]
      · exact absurd hxD (hafter t (hIccI ht) hlt)
    · rintro rfl
      exact ⟨⟨a, ⟨le_refl a, hbmem.1⟩, rfl⟩, haD⟩
  have hKw : f '' Icc a b ∩ Plane.closedSquare w r = {f b} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxD⟩
      rcases eq_or_lt_of_le ht.2 with heq | hlt
      · simp [heq]
      · exact absurd hxD (hbefore t ⟨ht.1, le_trans ht.2 hbmem.2⟩ hlt)
    · rintro rfl
      exact ⟨⟨b, ⟨hbmem.1, le_refl b⟩, rfl⟩, hbD⟩
  refine ⟨f '' Icc a b, f a, f b, hKsub, harc.isArc.isCompact, harc, hKv, hKw,
    Set.disjoint_left.2 fun x hxK hxV => ?_⟩
  
  
  rcases h.vertex_mem_edgeArc hlink hxV (hKsub hxK) with heq | heq
  · have hmem : x ∈ f '' Icc a b ∩ Plane.closedSquare v r :=
      ⟨hxK, by rw [heq]; exact Plane.mem_closedSquare_self v hr.le⟩
    rw [hKv, mem_singleton_iff] at hmem
    exact hpv (hmem ▸ heq)
  · have hmem : x ∈ f '' Icc a b ∩ Plane.closedSquare w r :=
      ⟨hxK, by rw [heq]; exact Plane.mem_closedSquare_self w hr.le⟩
    rw [hKw, mem_singleton_iff] at hmem
    exact hqw (hmem ▸ heq)

end Graph
