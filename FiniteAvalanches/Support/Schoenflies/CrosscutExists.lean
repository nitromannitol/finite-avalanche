/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/CrosscutExists.lean.
-/
import FiniteAvalanches.Support.Schoenflies.OuterChain

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




































































open Set Schoenflies
open scoped Graph

namespace Graph

 

section General

variable {α β : Type*} {G : Graph α β}

 




theorem IsPath.split_at_edge {u v : α} {W : List β} {g : β} (h : G.IsPath u W v) (hg : g ∈ W) :
    ∃ (W₁ W₂ : List β) (c d : α), W = W₁ ++ g :: W₂ ∧ G.IsPath u W₁ c ∧ G.IsLink g c d ∧
      G.IsPath d W₂ v ∧ c ∉ G.walkVertices d W₂ ∧
      ∀ z ∈ G.walkVertices u W₁, z ∈ G.walkVertices c (g :: W₂) → z = c := by
  induction h with
  | nil => simp at hg
  | @cons u w v f W hl hW hfresh ih =>
    rcases List.mem_cons.1 hg with rfl | hg'
    · exact ⟨[], W, u, w, rfl, .nil hl.left_mem, hl, hW, hfresh, fun z hz _ => by simpa using hz⟩
    obtain ⟨W₁, W₂, c, d, hWeq, h₁, hlg, h₂, hcd, hmeet⟩ := ih hg'
    have hsub₁ : W₁ ⊆ W := by rw [hWeq]; exact List.subset_append_left _ _
    have hsub₂ : g :: W₂ ⊆ W := by rw [hWeq]; exact List.subset_append_right _ _
    refine ⟨f :: W₁, W₂, c, d, by rw [hWeq]; rfl,
      .cons hl h₁ fun hmem => hfresh (walkVertices_mono hsub₁ hmem), hlg, h₂, hcd,
      fun z hz hz' => ?_⟩
    rcases mem_walkVertices_cons hl hz with hzu | hz''
    · 
      exfalso
      subst hzu
      refine hfresh ?_
      rcases mem_walkVertices_iff.1 hz' with heq | hcov
      · rw [heq]; exact walkVertices_mono hsub₁ h₁.target_mem_walkVertices
      · exact mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov)
    · exact hmeet z hz'' hz'

 


theorem IsCycleThrough.rotate {e g : β} {u v : α} {D : List β} (hc : G.IsCycleThrough e u v D)
    (hg : g ∈ e :: D) :
    ∃ (c d : α) (W : List β), G.IsCycleThrough g c d W ∧ (g :: W).Perm (e :: D) := by
  rcases List.mem_cons.1 hg with rfl | hgD
  · exact ⟨u, v, D, hc, List.Perm.refl _⟩
  obtain ⟨A, B, c, d, hD, hA, hlg, hB, hcd, hmeet⟩ := hc.isPath.split_at_edge hgD
  have hne : c ≠ d := fun hh => hcd (hh ▸ mem_walkVertices_self)
  have hY : G.IsPath c [g] d := IsPath.single hlg hne
  
  have hM2 : ∀ z ∈ G.walkVertices c [g], z ∈ G.walkVertices d B → z = d := by
    intro z hz hz'
    rcases mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, hinc⟩
    · exact absurd hz' hcd
    obtain rfl : f = g := by simpa using hf
    rcases hinc.eq_or_eq_of_isLink hlg with rfl | rfl
    · exact absurd hz' hcd
    · rfl
  obtain ⟨hpath, hperm, -⟩ :=
    hc.split_aux (X := A) (Y := [g]) (Z := B) (by rw [hD]; rfl) hA hY hB hne hmeet hM2
  
  have hnodup : (A ++ g :: B).Nodup := hD ▸ hc.isPath.nodup
  obtain ⟨-, hnd, -⟩ := List.nodup_append.1 hnodup
  have hgB : g ∉ B := (List.nodup_cons.1 hnd).1
  have hgA : g ∉ A := fun hmem =>
    List.disjoint_of_nodup_append hnodup hmem List.mem_cons_self
  have hge : g ≠ e := fun hh => hc.notMem (hh ▸ hgD)
  refine ⟨d, c, B ++ e :: A, ⟨hlg.symm, hpath, ?_⟩, hperm⟩
  simp only [List.mem_append, List.mem_cons, not_or]
  exact ⟨hgB, hge, hgA⟩

 
theorem IsCycleThrough.mem_walkVertices_of_inc {e f : β} {u v z : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (hf : f ∈ e :: D) (hz : G.Inc f z) :
    z ∈ G.walkVertices u D := by
  rcases List.mem_cons.1 hf with rfl | hfD
  · rcases hz.eq_or_eq_of_isLink hc.isLink with rfl | rfl
    · exact mem_walkVertices_self
    · exact hc.isPath.target_mem_walkVertices
  · exact mem_walkVertices_of_mem_covered ⟨f, hfD, hz⟩

 




theorem IsCycleThrough.split_at_edges {e g₁ g₂ : β} {u v : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (hg₁ : g₁ ∈ e :: D) (hg₂ : g₂ ∈ e :: D) (hne : g₁ ≠ g₂) :
    ∃ (p p' q q' : α) (W₁ W₂ : List β),
      G.IsLink g₁ p' p ∧ G.IsPath p W₁ q ∧ G.IsLink g₂ q q' ∧ G.IsPath q' W₂ p' ∧
        (g₁ :: (W₁ ++ g₂ :: W₂)).Perm (e :: D) ∧
        Disjoint (G.walkVertices p W₁) (G.walkVertices q' W₂) ∧
        G.walkVertices u D = G.walkVertices p W₁ ∪ G.walkVertices q' W₂ := by
  obtain ⟨p, p', Wc, hrot, hrperm⟩ := hc.rotate hg₁
  have hg₂c : g₂ ∈ Wc := by
    rcases List.mem_cons.1 (hrperm.mem_iff.2 hg₂) with rfl | hmem
    · exact absurd rfl hne
    · exact hmem
  obtain ⟨W₁, W₂, q, q', hWc, hW₁, hlg₂, hW₂, hqfresh, hmeet⟩ := hrot.isPath.split_at_edge hg₂c
  have hperm : (g₁ :: (W₁ ++ g₂ :: W₂)).Perm (e :: D) := by rw [← hWc]; exact hrperm
  
  
  have hsub : G.walkVertices q' W₂ ⊆ G.walkVertices q (g₂ :: W₂) := by
    intro z hz
    rcases mem_walkVertices_iff.1 hz with rfl | hcov
    · exact mem_walkVertices_of_mem_covered ⟨g₂, List.mem_cons_self, hlg₂.inc_right⟩
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hcov)
  have hdisj : Disjoint (G.walkVertices p W₁) (G.walkVertices q' W₂) := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    obtain rfl : z = q := hmeet z hz₁ (hsub hz₂)
    exact hqfresh hz₂
  
  have hmemC : ∀ (f : β) (z : α), f ∈ e :: D → G.Inc f z → z ∈ G.walkVertices u D :=
    fun _ _ hf hz => hc.mem_walkVertices_of_inc hf hz
  refine ⟨p, p', q, q', W₁, W₂, hrot.isLink.symm, hW₁, hlg₂, hW₂, hperm, hdisj,
    Set.Subset.antisymm (fun z hz => ?_) (Set.union_subset (fun z hz => ?_) fun z hz => ?_)⟩
  · 
    have hcov : z ∈ G.coveredVertices (e :: D) := by
      rcases mem_walkVertices_iff.1 hz with rfl | hcov
      · exact ⟨e, List.mem_cons_self, hc.isLink.inc_left⟩
      · exact coveredVertices_mono (List.subset_cons_self _ _) hcov
    obtain ⟨f, hf, hinc⟩ := hcov
    rcases List.mem_cons.1 (hperm.mem_iff.2 hf) with rfl | hf'
    · rcases hinc.eq_or_eq_of_isLink hrot.isLink with rfl | rfl
      · exact Or.inl mem_walkVertices_self
      · exact Or.inr hW₂.target_mem_walkVertices
    rcases List.mem_append.1 hf' with hf'' | hf''
    · exact Or.inl (mem_walkVertices_of_mem_covered ⟨f, hf'', hinc⟩)
    rcases List.mem_cons.1 hf'' with rfl | hf'''
    · rcases hinc.eq_or_eq_of_isLink hlg₂ with rfl | rfl
      · exact Or.inl hW₁.target_mem_walkVertices
      · exact Or.inr mem_walkVertices_self
    · exact Or.inr (mem_walkVertices_of_mem_covered ⟨f, hf''', hinc⟩)
  · rcases mem_walkVertices_iff.1 hz with heq | ⟨f, hf, hinc⟩
    · rw [heq]; exact hmemC g₁ p hg₁ hrot.isLink.inc_left
    · exact hmemC f z (hperm.mem_iff.1 (List.mem_cons_of_mem _ (List.mem_append_left _ hf))) hinc
  · rcases mem_walkVertices_iff.1 hz with heq | ⟨f, hf, hinc⟩
    · rw [heq]; exact hmemC g₂ q' hg₂ hlg₂.inc_right
    · exact hmemC f z (hperm.mem_iff.1
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hf)))) hinc

 

 










theorem exists_isCycleCrosscut {H F : Graph α β} {e : β} {u v : α} {D : List β}
    (hcyc : H.IsCycleThrough e u v D) (hFH : F ≤ H) {S₁ S₂ : Set α}
    (hdisj : Disjoint S₁ S₂) (hcover : H.walkVertices u D = S₁ ∪ S₂)
    (hpres : ∀ f ∈ e :: D, f ∈ E(F) → ∀ z w, H.IsLink f z w → (z ∈ S₁ ↔ w ∈ S₁))
    (hconn : F.Connected) (ha : ∃ a ∈ S₁, a ∈ V(F)) (hb : ∃ b ∈ S₂, b ∈ V(F)) :
    ∃ (a b : α) (R D₁ D₂ : List β), IsCycleCrosscut H F e u v D a b R D₁ D₂ := by
  classical
  
  have hside : ∀ (a' b' : α) (T : List β), H.IsWalk a' T b' → (∀ f ∈ T, f ∈ E(F)) →
      (∀ f ∈ T, f ∈ e :: D) → a' ∈ S₁ → b' ∈ S₁ := by
    intro a' b' T hw
    induction hw with
    | nil => exact fun _ _ hm => hm
    | @cons z w b' f T hl hW ih =>
      intro hFe hCe hz
      exact ih (fun f' hf' => hFe f' (List.mem_cons_of_mem _ hf'))
        (fun f' hf' => hCe f' (List.mem_cons_of_mem _ hf'))
        ((hpres f (hCe f List.mem_cons_self) (hFe f List.mem_cons_self) z w hl).1 hz)
  
  obtain ⟨a₀, ha₀S, ha₀F⟩ := ha
  obtain ⟨b₀, hb₀S, hb₀F⟩ := hb
  have hex : ∃ k, ∃ (T : List β) (a b : α),
      T.length = k ∧ F.IsWalk a T b ∧ a ∈ S₁ ∧ b ∈ S₂ := by
    obtain ⟨T, hT⟩ := hconn.reaches ha₀F hb₀F
    exact ⟨T.length, T, a₀, b₀, rfl, hT, ha₀S, hb₀S⟩
  obtain ⟨T, a, b, hTlen, hTwalk, haS, hbS⟩ := Nat.find_spec hex
  have hmin : ∀ (T' : List β) (a' b' : α), F.IsWalk a' T' b' → a' ∈ S₁ → b' ∈ S₂ →
      T.length ≤ T'.length := by
    intro T' a' b' hw' h1 h2
    rw [hTlen]
    exact Nat.find_le ⟨T', a', b', rfl, hw', h1, h2⟩
  
  have hR : F.IsPath a T b := hTwalk.isPath_of_minLength fun W' hW' => hmin W' a b hW' haS hbS
  have hTedges : ∀ f ∈ T, f ∈ E(F) := fun f hf => hR.edge_mem hf
  have hab : a ≠ b := by
    rintro rfl
    exact Set.disjoint_left.1 hdisj haS hbS
  have haC : a ∈ H.walkVertices u D := by rw [hcover]; exact Or.inl haS
  have hbC : b ∈ H.walkVertices u D := by rw [hcover]; exact Or.inr hbS
  obtain ⟨D₁, D₂, harc₁, harc₂, hsplit, -⟩ := hcyc.split_at haC hbC hab
  
  have hTvert : H.walkVertices a T = F.walkVertices a T := walkVertices_congr_of_le hFH hTedges
  have hinterior : ∀ y ∈ H.walkVertices a T, y ≠ a → y ≠ b → y ∉ H.walkVertices u D := by
    intro y hy hya hyb hyC
    rw [hTvert] at hy
    obtain ⟨T₁, T₂, hTcat, hT₁, hT₂, -⟩ := hR.split hy
    have hlen₁ : 1 ≤ T₁.length := by
      cases T₁ with
      | nil => exact absurd hT₁.isWalk.eq_of_nil.symm hya
      | cons _ _ => simp
    have hlen₂ : 1 ≤ T₂.length := by
      cases T₂ with
      | nil => exact absurd hT₂.isWalk.eq_of_nil hyb
      | cons _ _ => simp
    have hcat : T.length = T₁.length + T₂.length := by rw [hTcat, List.length_append]
    rw [hcover] at hyC
    rcases hyC with hy₁ | hy₂
    · have := hmin T₂ y b hT₂.isWalk hy₁ hbS
      omega
    · have := hmin T₁ a y hT₁.isWalk haS hy₂
      omega
  
  have hedges_new : ∀ f ∈ T, f ∉ D ++ [e] := by
    intro f hf hfC
    have hfC' : f ∈ e :: D := by
      simp only [List.mem_append, List.mem_cons] at hfC ⊢
      tauto
    have hfF : f ∈ E(F) := hTedges f hf
    obtain ⟨z, w, hlfF⟩ := exists_isLink_of_mem_edgeSet hfF
    have hlf : H.IsLink f z w := hlfF.mono hFH
    have hz' : z = a ∨ z = b := by
      by_contra hcon
      push Not at hcon
      exact hinterior z (mem_walkVertices_of_mem_covered ⟨f, hf, hlf.inc_left⟩) hcon.1 hcon.2
        (hcyc.mem_walkVertices_of_inc hfC' hlf.inc_left)
    have hw' : w = a ∨ w = b := by
      by_contra hcon
      push Not at hcon
      exact hinterior w (mem_walkVertices_of_mem_covered ⟨f, hf, hlf.inc_right⟩) hcon.1 hcon.2
        (hcyc.mem_walkVertices_of_inc hfC' hlf.inc_right)
    have hzw : z ≠ w := by
      rintro rfl
      exact hR.not_isLoopAt hf z hlfF
    
    have hlink : H.IsLink f a b := by
      rcases hz' with rfl | rfl
      · rcases hw' with rfl | rfl
        · exact absurd rfl hzw
        · exact hlf
      · rcases hw' with rfl | rfl
        · exact hlf.symm
        · exact absurd rfl hzw
    refine Set.disjoint_left.1 hdisj (hside a b [f] (IsWalk.single hlink) ?_ ?_ haS) hbS
    · intro f' hf'
      rw [List.mem_singleton.1 hf']
      exact hfF
    · intro f' hf'
      rw [List.mem_singleton.1 hf']
      exact hfC'
  
  have houtside : ∀ (T' : List β), H.IsWalk a T' b → (∀ f ∈ T', f ∈ e :: D) →
      ∃ f ∈ T', f ∉ E(F) := by
    intro T' hw hC
    by_contra hcon
    push Not at hcon
    exact Set.disjoint_left.1 hdisj (hside a b T' hw hcon hC haS) hbS
  have hD₁C : ∀ f ∈ D₁, f ∈ e :: D :=
    fun f hf => hsplit.mem_iff.1 (List.mem_append_left _ hf)
  have hD₂C : ∀ f ∈ D₂, f ∈ e :: D :=
    fun f hf => hsplit.mem_iff.1 (List.mem_append_right _ hf)
  obtain ⟨f₂, hf₂, hf₂F⟩ := houtside D₂.reverse harc₂.reverse.isWalk
    fun f hf => hD₂C f (List.mem_reverse.1 hf)
  exact ⟨a, b, T, D₁, D₂,
    { ne := hab
      arc₁ := harc₁
      arc₂ := harc₂
      split := hsplit
      isPath := hR.mono hFH
      mem_left := haC
      mem_right := hbC
      edges_mem := hTedges
      edges_new := hedges_new
      interior := hinterior
      outside₁ := houtside D₁ harc₁.isWalk hD₁C
      outside₂ := ⟨f₂, List.mem_reverse.1 hf₂, hf₂F⟩ }⟩

end General

 

section Chain

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {n : ℕ}

 










theorem IsPlaneChain.crosscutExists (h : IsPlaneChain Γ drawing G n) {x : Plane} :
    CrosscutExists Γ drawing n x := by
  intro i m him e u v D hcyc _hin hA hB
  obtain ⟨gA, hgAC, hgAJ, hgAF⟩ := hA
  obtain ⟨gB, hgBC, hgBL, hgBF⟩ := hB
  
  have hFH : Γ (i + m + 1) ≤ chainUnion Γ i (m + 2) := h.le_block him (by omega) (by omega)
  have hJH : Γ (i + m + 2) ≤ chainUnion Γ i (m + 2) := h.le_block him (by omega) (by omega)
  have hLH : chainUnion Γ i m ≤ chainUnion Γ i (m + 2) :=
    chainUnion_le fun p hp _ => h.le_block him hp (by omega)
  
  have hsplit : ∀ f ∈ E(chainUnion Γ i (m + 2)),
      f ∈ E(chainUnion Γ i m) ∨ f ∈ E(Γ (i + m + 1)) ∨ f ∈ E(Γ (i + m + 2)) := by
    intro f hf
    obtain ⟨p, hp, hp', hfp⟩ := mem_edgeSet_chainUnion.1 hf
    rcases Nat.lt_or_ge p (i + m + 1) with hlt | hge
    · exact Or.inl (mem_edgeSet_chainUnion.2 ⟨p, hp, by omega, hfp⟩)
    rcases Nat.lt_or_ge p (i + m + 2) with hlt' | hge'
    · obtain rfl : p = i + m + 1 := by omega
      exact Or.inr (Or.inl hfp)
    · obtain rfl : p = i + m + 2 := by omega
      exact Or.inr (Or.inr hfp)
  
  have hVdisj : ∀ z : Plane, z ∈ V(chainUnion Γ i m) → z ∈ V(Γ (i + m + 2)) → False := by
    intro z hz hz'
    exact Set.disjoint_left.1 (h.disjoint_block_far (by omega))
      (vertexSet_subset_pointSet hz) (vertexSet_subset_pointSet hz')
  have hgAB : gA ≠ gB := by
    rintro rfl
    obtain ⟨p, hp, hp', hgp⟩ := mem_edgeSet_chainUnion.1 hgBL
    exact Set.disjoint_left.1
      (h.disjoint_edgeSet (p := p) (q := i + m + 2) (by omega) (by omega) (by omega)) hgp hgAJ
  obtain ⟨p₀, p₁, q₀, q₁, W₁, W₂, hlA, hW₁, hlB, hW₂, hperm, hdisj, hcover⟩ :=
    hcyc.split_at_edges hgAC hgBC hgAB
  have hlAJ : (Γ (i + m + 2)).IsLink gA p₁ p₀ := (hJH.isLink_iff hgAJ).2 hlA
  have hlBL : (chainUnion Γ i m).IsLink gB q₀ q₁ := (hLH.isLink_iff hgBL).2 hlB
  
  
  have hpres : ∀ f ∈ e :: D, f ∈ E(Γ (i + m + 1)) → ∀ z w : Plane,
      (chainUnion Γ i (m + 2)).IsLink f z w →
      (z ∈ (chainUnion Γ i (m + 2)).walkVertices p₀ W₁ ↔
        w ∈ (chainUnion Γ i (m + 2)).walkVertices p₀ W₁) := by
    intro f hfC hfF z w hlf
    have hfA : f ≠ gA := fun hh => hgAF (hh ▸ hfF)
    have hfB : f ≠ gB := fun hh => hgBF (hh ▸ hfF)
    have hfW : f ∈ W₁ ∨ f ∈ W₂ := by
      rcases List.mem_cons.1 (hperm.mem_iff.2 hfC) with rfl | hmem
      · exact absurd rfl hfA
      rcases List.mem_append.1 hmem with hmem' | hmem'
      · exact Or.inl hmem'
      rcases List.mem_cons.1 hmem' with rfl | hmem''
      · exact absurd rfl hfB
      · exact Or.inr hmem''
    rcases hfW with hfW | hfW
    · exact iff_of_true (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_left⟩)
        (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_right⟩)
    · refine iff_of_false (fun hz => ?_) fun hw => ?_
      · exact Set.disjoint_left.1 hdisj hz
          (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_left⟩)
      · exact Set.disjoint_left.1 hdisj hw
          (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_right⟩)
  
  have hclaimA : ∃ a ∈ (chainUnion Γ i (m + 2)).walkVertices p₀ W₁, a ∈ V(Γ (i + m + 1)) := by
    have hwalk : (chainUnion Γ i (m + 2)).IsWalk p₁ (gA :: (W₁ ++ [gB])) q₁ :=
      .cons hlA (hW₁.isWalk.append (IsWalk.single hlB))
    obtain ⟨f, hf, z, w, hlf, hzJ, hwJ⟩ := hwalk.crossing (S := V(Γ (i + m + 2)))
      hlAJ.left_mem fun hh => hVdisj q₁ hlBL.right_mem hh
    have hfJ : f ∉ E(Γ (i + m + 2)) := fun hh => hwJ ((hJH.isLink_iff hh).2 hlf).right_mem
    have hfL : f ∉ E(chainUnion Γ i m) := fun hh =>
      hVdisj z ((hLH.isLink_iff hh).2 hlf).left_mem hzJ
    have hfF : f ∈ E(Γ (i + m + 1)) := by
      rcases hsplit f hlf.edge_mem with hh | hh | hh
      · exact absurd hh hfL
      · exact hh
      · exact absurd hh hfJ
    have hfW₁ : f ∈ W₁ := by
      rcases List.mem_cons.1 hf with rfl | hf'
      · exact absurd hfF hgAF
      rcases List.mem_append.1 hf' with hf'' | hf''
      · exact hf''
      · obtain rfl : f = gB := by simpa using hf''
        exact absurd hfF hgBF
    exact ⟨z, mem_walkVertices_of_mem_covered ⟨f, hfW₁, hlf.inc_left⟩,
      ((hFH.isLink_iff hfF).2 hlf).left_mem⟩
  
  have hclaimB : ∃ b ∈ (chainUnion Γ i (m + 2)).walkVertices q₁ W₂, b ∈ V(Γ (i + m + 1)) := by
    have hwalk : (chainUnion Γ i (m + 2)).IsWalk q₁ (W₂ ++ [gA]) p₀ :=
      hW₂.isWalk.append (IsWalk.single hlA)
    obtain ⟨f, hf, z, w, hlf, hzL, hwL⟩ := hwalk.crossing (S := V(chainUnion Γ i m))
      hlBL.right_mem fun hh => hVdisj p₀ hh hlAJ.right_mem
    have hfL : f ∉ E(chainUnion Γ i m) := fun hh => hwL ((hLH.isLink_iff hh).2 hlf).right_mem
    have hfJ : f ∉ E(Γ (i + m + 2)) := fun hh =>
      hVdisj z hzL ((hJH.isLink_iff hh).2 hlf).left_mem
    have hfF : f ∈ E(Γ (i + m + 1)) := by
      rcases hsplit f hlf.edge_mem with hh | hh | hh
      · exact absurd hh hfL
      · exact hh
      · exact absurd hh hfJ
    have hfW₂ : f ∈ W₂ := by
      rcases List.mem_append.1 hf with hf' | hf'
      · exact hf'
      · obtain rfl : f = gA := by simpa using hf'
        exact absurd hfF hgAF
    exact ⟨z, mem_walkVertices_of_mem_covered ⟨f, hfW₂, hlf.inc_left⟩,
      ((hFH.isLink_iff hfF).2 hlf).left_mem⟩
  exact exists_isCycleCrosscut hcyc hFH hdisj hcover hpres
    (h.twoConnected _ (by omega)).connected hclaimA hclaimB

end Chain

end Graph
