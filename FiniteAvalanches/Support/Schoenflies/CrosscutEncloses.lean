/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/CrosscutEncloses.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.OuterChain
import FiniteAvalanches.Support.Schoenflies.CombinatorialInvariance

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





























































































open Bornology Set

namespace Schoenflies

 







 






theorem two_arcs_inter_of_union {C A₁ A₂ : Set Plane} {p q : Plane} (hC : IsJordanCurve C)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C) :
    A₁ ∩ A₂ = {p, q} := by
  have hpq : p ≠ q := hA1.ne
  have hpC : p ∈ C := by rw [← hunion]; exact Or.inl hA1.left_mem
  have hqC : q ∈ C := by rw [← hunion]; exact Or.inl hA1.right_mem
  obtain ⟨B₁, B₂, hB1, hB2, hBunion, hBinter⟩ := hC.two_arcs hpC hqC hpq
  have hB1C : B₁ ⊆ C := by rw [← hBunion]; exact Set.subset_union_left
  have hB2C : B₂ ⊆ C := by rw [← hBunion]; exact Set.subset_union_right
  have hA1C : A₁ ⊆ C := by rw [← hunion]; exact Set.subset_union_left
  have hA2C : A₂ ⊆ C := by rw [← hunion]; exact Set.subset_union_right
  
  have key : ∀ A : Set Plane, IsArcBetween A p q → A ⊆ C → A ⊆ B₁ ∨ A ⊆ B₂ := by
    intro A hAar hAC
    obtain ⟨hconn, hne⟩ := hAar.preconnected_diff
    have hsub : A \ {p, q} ⊆ B₁ᶜ ∪ B₂ᶜ := by
      intro w hw
      by_cases h1 : w ∈ B₁
      · by_cases h2 : w ∈ B₂
        · exact absurd (show w ∈ ({p, q} : Set Plane) by rw [← hBinter]; exact ⟨h1, h2⟩) hw.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (B₁ᶜ ∩ B₂ᶜ)).Nonempty := by
      rintro ⟨w, hw, h1, h2⟩
      have hwC : w ∈ C := hAC hw.1
      rw [← hBunion] at hwC
      exact hwC.elim h1 h2
    have hends : ∀ B : Set Plane, p ∈ B → q ∈ B → A \ {p, q} ⊆ B → A ⊆ B := by
      intro B hpB hqB hsub' w hw
      by_cases hwpq : w ∈ ({p, q} : Set Plane)
      · rcases hwpq with rfl | rfl
        exacts [hpB, hqB]
      · exact hsub' ⟨hw, hwpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ B₁ᶜ).Nonempty
    · refine Or.inr (hends B₂ hB2.left_mem hB2.right_mem fun w hw => ?_)
      by_contra hwB2
      exact hnone (hconn _ _ hB1.isArc.isClosed.isOpen_compl hB2.isArc.isClosed.isOpen_compl
        hsub hcase ⟨w, hw, hwB2⟩)
    · refine Or.inl (hends B₁ hB1.left_mem hB1.right_mem fun w hw => ?_)
      by_contra hwB1
      exact hcase ⟨w, hw, hwB1⟩
  
  have hbig : ∀ A : Set Plane, IsArcBetween A p q → ¬ A ⊆ ({p, q} : Set Plane) := by
    intro A hAar hsub
    obtain ⟨-, w, hw⟩ := hAar.preconnected_diff
    exact hw.2 (hsub hw.1)
  
  have hclash : ∀ B B' : Set Plane, B ∪ B' = C → B ∩ B' = {p, q} → IsArcBetween B' p q →
      A₁ ⊆ B → A₂ ⊆ B → False := by
    intro B B' hBB hBBi hB' h1 h2
    refine hbig B' hB' fun w hw => ?_
    rw [← hBBi]
    have hwC : w ∈ C := by rw [← hBB]; exact Or.inr hw
    rw [← hunion] at hwC
    exact hwC.elim (fun h => ⟨h1 h, hw⟩) fun h => ⟨h2 h, hw⟩
  
  have hfill : ∀ X Y X' Y' : Set Plane, X ∪ Y = C → X' ∩ Y' = {p, q} → X' ⊆ C →
      p ∈ X → q ∈ X → X ⊆ X' → Y ⊆ Y' → X = X' := by
    intro X Y X' Y' hXY hX'Y'i hX'C hpX hqX hXX hYY
    refine Set.Subset.antisymm hXX fun w hw => ?_
    have hwC : w ∈ C := hX'C hw
    rw [← hXY] at hwC
    rcases hwC with h | h
    · exact h
    · have hwpq : w ∈ ({p, q} : Set Plane) := by rw [← hX'Y'i]; exact ⟨hw, hYY h⟩
      rcases hwpq with rfl | rfl
      exacts [hpX, hqX]
  rcases key A₁ hA1 hA1C with h1 | h1 <;> rcases key A₂ hA2 hA2C with h2 | h2
  · exact absurd (hclash B₁ B₂ hBunion hBinter hB2 h1 h2) (by simp)
  · rw [hfill A₁ A₂ B₁ B₂ hunion hBinter hB1C hA1.left_mem hA1.right_mem h1 h2,
      hfill A₂ A₁ B₂ B₁ (by rw [Set.union_comm]; exact hunion)
        (by rw [Set.inter_comm]; exact hBinter) hB2C hA2.left_mem hA2.right_mem h2 h1]
    exact hBinter
  · rw [hfill A₁ A₂ B₂ B₁ hunion (by rw [Set.inter_comm]; exact hBinter) hB2C
        hA1.left_mem hA1.right_mem h1 h2,
      hfill A₂ A₁ B₁ B₂ (by rw [Set.union_comm]; exact hunion) hBinter hB1C
        hA2.left_mem hA2.right_mem h2 h1, Set.inter_comm]
    exact hBinter
  · exact absurd (hclash B₂ B₁ (by rw [Set.union_comm]; exact hBunion)
      (by rw [Set.inter_comm]; exact hBinter) hB1 h1 h2) (by simp)

 




 















theorem crosscut_inside_at_least_one {J A₁ A₂ P : Set Plane} {p q x : Plane}
    (hJ : IsJordanCurve J) (hJpoly : IsPolygonal J) (hPpoly : IsPolygonal P)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = J)
    (hParc : IsArcBetween P p q) (hPJ : P ∩ J = {p, q})
    (hx : x ∈ inside J) (hxP : x ∉ P) :
    x ∈ inside (A₁ ∪ P) ∨ x ∈ inside (A₂ ∪ P) := by
  have hpq : p ≠ q := hA1.ne
  have hinter : A₁ ∩ A₂ = {p, q} := two_arcs_inter_of_union hJ hA1 hA2 hunion
  have hpJ : p ∈ J := by rw [← hunion]; exact Or.inl hA1.left_mem
  have hqJ : q ∈ J := by rw [← hunion]; exact Or.inl hA1.right_mem
  
  obtain ⟨m, C, a, k, hcar, hva, hvb, hk1, hk2⟩ := exists_prePolygon_split hJ hJpoly hpJ hqJ hpq
  have hk3 : k ≤ m + 3 := by omega
  have hDunion : C.arc a k ∪ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = J := by
    rw [C.arc_union a hk3, hcar]
  have hDinter : C.arc a k ∩ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [C.arc_inter a hk1 hk2, hva, hvb]
  have hD1n : ¬ C.arc a k ⊆ ({p, q} : Set Plane) := by
    rw [← hva, ← hvb]; exact C.arc_not_subset_endpoints a hk1 hk2
  have hD2n : ¬ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ ({p, q} : Set Plane) := by
    have h := C.arc_not_subset_endpoints (a + (k : ZMod (m + 3))) (k := m + 3 - k)
      (by omega) (by omega)
    rw [zmod_add_sub_cancel hk3 a, hva, hvb, Set.pair_comm q p] at h
    exact h
  
  have hids := two_arcs_unique_of_isClosed hunion hinter hDunion hDinter hA1 hA2
    (C.isCompact_arc a k).isClosed (C.isCompact_arc _ _).isClosed hD1n hD2n
  have harc1 : IsArcBetween (C.arc a k) p q := by
    rcases hids with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact e1 ▸ hA1
    · exact e2 ▸ hA2
  have harc2 : IsArcBetween (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    rcases hids with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact e2 ▸ hA2
    · exact e1 ▸ hA1
  have hD1J : C.arc a k ⊆ J := by rw [← hcar]; exact C.arc_subset_carrier a k
  have hD2J : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ J := by
    rw [← hcar]; exact C.arc_subset_carrier _ _
  
  obtain ⟨ws, hwsne, hwhead, hwlast, hwpoly⟩ := hParc.exists_poly_eq hPpoly hpq
  obtain ⟨ws', hwsne', hwhead', hwlast', hwpoly'⟩ := hParc.reverse.exists_poly_eq hPpoly hpq.symm
  have hKcover : cover (segsOf ws) = P := by
    rw [cover_segsOf_eq (a := p) (b := q) (by rw [hwpoly]; exact hParc.left_mem)
      (by rw [hwpoly]; exact hParc.right_mem) hpq, hwpoly]
  have hKchain : IsChainFrom (segsOf ws) p q := by
    have h := isChainFrom_segsOf ws hwsne
    rwa [hwhead, hwlast] at h
  
  have hpolyD1P : IsPolygonal (C.arc a k ∪ P) :=
    ⟨C.arcList a k ++ ws', by
      rw [poly_append_of_eq (C.arcList_ne_nil a k) hwsne'
          (by rw [PrePolygon.getLast_arcList k C a, hvb, hwhead']),
        PrePolygon.poly_arcList_of_pos C a hk1, hwpoly']⟩
  have hpolyD2P : IsPolygonal (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    ⟨C.arcList (a + (k : ZMod (m + 3))) (m + 3 - k) ++ ws, by
      rw [poly_append_of_eq (C.arcList_ne_nil _ _) hwsne
          (by rw [PrePolygon.getLast_arcList (m + 3 - k) C _, zmod_add_sub_cancel hk3 a, hva,
            hwhead]),
        PrePolygon.poly_arcList_of_pos C _ (by omega : 1 ≤ m + 3 - k), hwpoly]⟩
  have hmeetP : ∀ (S : Set Plane), S ⊆ J → ∀ w ∈ S, w ∈ P → w = p ∨ w = q := by
    intro S hSJ w hw hwP
    have hmem : w ∈ ({p, q} : Set Plane) := by rw [← hPJ]; exact ⟨hwP, hSJ hw⟩
    simpa using hmem
  have hJ1 : IsSeparating (C.arc a k ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc1 hParc (hmeetP _ hD1J)) hpolyD1P
  have hJ2 : IsSeparating (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc2 hParc (hmeetP _ hD2J)) hpolyD2P
  
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ segsOf ws) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with h | h
    · exact C.pieces_nondeg Q h
    · exact segsOf_nondeg ws Q h)
  have hlevC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_left _ hQ)
  have hlevK : ∀ Q ∈ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)
  have hlev1 : ∀ Q ∈ C.arcPieces a k ++ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hlev2 : ∀ Q ∈ C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws,
      hgt u Q.1 ≠ hgt u Q.2 := hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hchain1 : IsChainFrom (C.arcPieces a k) p q := by
    have h := C.isChainFrom_arcPieces a k
    rwa [hva, hvb] at h
  have hchain2 : IsChainFrom (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)) q p := by
    have h := C.isChainFrom_arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)
    rw [zmod_add_sub_cancel hk3 a] at h
    rwa [hva, hvb] at h
  have hclosed1 : IsClosedChain (C.arcPieces a k ++ segsOf ws) :=
    hchain1.isClosedChain_append hKchain
  have hclosed2 : IsClosedChain
      (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) :=
    isChainFrom_self_iff.1 (hchain2.append hKchain)
  have hcov1 : cover (C.arcPieces a k ++ segsOf ws) = C.arc a k ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hcov2 : cover (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws)
      = C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
    rw [cover_append, hKcover]
    rfl
  
  have hsplit : ∀ w : Plane,
      parity u (C.arcPieces a k ++ segsOf ws) w
        + parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u C.pieces w :=
    fun w => parity_split u (C.sameEdges_arcPieces_split a hk3) (List.Perm.refl _)
      (List.Perm.refl _) w
  
  have main : x ∈ inside (C.arc a k ∪ P) ∨
      x ∈ inside (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have hxJ : x ∉ J := (mem_inside_iff.1 hx).1
    have hx1 : x ∉ C.arc a k ∪ P := by
      rintro (h | h)
      exacts [hxJ (hD1J h), hxP h]
    have hx2 : x ∉ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
      rintro (h | h)
      exacts [hxJ (hD2J h), hxP h]
    have hout1 : x ∈ outside (C.arc a k ∪ P) := by
      have hm : x ∈ inside (C.arc a k ∪ P) ∪ outside (C.arc a k ∪ P) := by
        rw [inside_union_outside]; exact hx1
      exact hm.resolve_left hn1
    have hout2 : x ∈ outside (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) := by
      have hm : x ∈ inside (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) ∪
          outside (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) := by
        rw [inside_union_outside]; exact hx2
      exact hm.resolve_left hn2
    have hp1 : parity u (C.arcPieces a k ++ segsOf ws) x = 0 :=
      parity_eq_zero_of_mem_outside_cover hu hlev1 hclosed1 (by rw [hcov1]; exact hJ1)
        (by rw [hcov1]; exact hout1)
    have hp2 : parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) x = 0 :=
      parity_eq_zero_of_mem_outside_cover hu hlev2 hclosed2 (by rw [hcov2]; exact hJ2)
        (by rw [hcov2]; exact hout2)
    have hkey := hsplit x
    rw [hp1, hp2, C.parity_eq_one_of_mem_inside hu hlevC
      (show x ∈ inside C.carrier by rw [hcar]; exact hx)] at hkey
    exact absurd hkey (by decide)
  
  rcases hids with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]; exact main
  · rw [e1, e2]; exact main.symm

end Schoenflies

namespace Graph

open scoped Graph

open Schoenflies

variable {β : Type*} {H F : Graph Plane β} {drawing : β → ℝ → Plane}

 




 

theorem IsDrawing.mem_edgesCover_of_mem_walkVertices (h : IsDrawing H drawing) {u v y : Plane}
    {W : List β} (hW : H.IsWalk u W v) (hne : W ≠ []) (hy : y ∈ H.walkVertices u W) :
    y ∈ edgesCover drawing W := by
  rcases mem_walkVertices_iff.1 hy with rfl | ⟨g, hg, hinc⟩
  · exact hW.left_mem_edgesCover h hne
  · exact mem_edgesCover hg (h.inc_mem_edgeArc hinc)

 



 







def CrosscutEnclosesOff (drawing : β → ℝ → Plane) (x : Plane) : Prop :=
  ∀ (H F : Graph Plane β), H.Finite → IsDrawing H drawing →
    (∀ g ∈ E(H), IsPolygonal (edgeArc drawing g)) → x ∈ exterior H drawing →
    ∀ (e : β) (u v a b : Plane) (D R D₁ D₂ : List β),
      H.IsCycleThrough e u v D → IsCycleCrosscut H F e u v D a b R D₁ D₂ →
      x ∈ inside (edgesCover drawing (e :: D)) →
      ∀ (e₁ e₂ : β) (u₁ v₁ u₂ v₂ : Plane) (T₁ T₂ : List β),
        H.IsCycleThrough e₁ u₁ v₁ T₁ → H.IsCycleThrough e₂ u₂ v₂ T₂ →
        (e₁ :: T₁).Perm (D₁ ++ R) → (e₂ :: T₂).Perm (D₂ ++ R) →
        x ∈ inside (edgesCover drawing (e₁ :: T₁)) ∨
          x ∈ inside (edgesCover drawing (e₂ :: T₂))

 











theorem crosscutEnclosesOff (drawing : β → ℝ → Plane) (x : Plane) :
    CrosscutEnclosesOff drawing x := by
  intro H F _ hd hpoly hxext e u v a b D R D₁ D₂ hcyc hcc hin e₁ e₂ u₁ v₁ u₂ v₂ T₁ T₂ _ _ hp₁ hp₂
  have hab : a ≠ b := hcc.ne
  have hRne : R ≠ [] := hcc.isPath.ne_nil hab
  have hD1ne : D₁ ≠ [] := hcc.arc₁.ne_nil hab
  have hD2ne : D₂ ≠ [] := hcc.arc₂.ne_nil hab.symm
  
  have hDne : D ≠ [] := fun h0 =>
    hd.ne_of_isLink hcyc.isLink (h0 ▸ hcyc.isPath.isWalk).eq_of_nil
  
  have hJcurve : IsJordanCurve (edgesCover drawing (e :: D)) := hd.cycle_isJordanCurve hcyc
  have hJpoly : IsPolygonal (edgesCover drawing (e :: D)) :=
    hd.isPolygonal_edgesCover hpoly hcyc.isWalk_cons (List.cons_ne_nil _ _)
  have hPpoly : IsPolygonal (edgesCover drawing R) :=
    hd.isPolygonal_edgesCover hpoly hcc.isPath.isWalk hRne
  have hA1 : IsArcBetween (edgesCover drawing D₁) a b := hd.path_isArcBetween hcc.arc₁ hD1ne
  have hA2 : IsArcBetween (edgesCover drawing D₂) a b :=
    (hd.path_isArcBetween hcc.arc₂ hD2ne).reverse
  have hParc : IsArcBetween (edgesCover drawing R) a b := hd.path_isArcBetween hcc.isPath hRne
  
  have hunion : edgesCover drawing D₁ ∪ edgesCover drawing D₂ = edgesCover drawing (e :: D) := by
    rw [← edgesCover_append]
    exact edgesCover_perm hcc.split
  
  have hcut : ∀ y : Plane, y ∈ H.walkVertices u D → y ∈ edgesCover drawing (e :: D) := by
    intro y hy
    exact edgesCover_mono (fun g hg => List.mem_cons_of_mem _ hg)
      (hd.mem_edgesCover_of_mem_walkVertices hcyc.isPath.isWalk hDne hy)
  
  
  
  have hPJ : edgesCover drawing R ∩ edgesCover drawing (e :: D) = {a, b} := by
    refine Set.Subset.antisymm (fun z hz => ?_) ?_
    · obtain ⟨hzR, hzJ⟩ := hz
      obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hzR
      obtain ⟨g', hg', hzg'⟩ := mem_edgesCover_iff.1 hzJ
      have hne : g ≠ g' := by
        rintro rfl
        refine hcc.edges_new g hg ?_
        rcases List.mem_cons.1 hg' with rfl | h
        · exact List.mem_append_right _ (List.mem_singleton_self _)
        · exact List.mem_append_left _ h
      obtain ⟨-, hincg, hincg'⟩ := hd.edge_inter (hcc.isPath.edge_mem hg)
        (hcyc.mem_edgeSet_cons hg') hne hzg hzg'
      have hzR' : z ∈ H.walkVertices a R := mem_walkVertices_of_mem_covered ⟨g, hg, hincg⟩
      have hzD : z ∈ H.walkVertices u D := by
        rcases List.mem_cons.1 hg' with rfl | h
        · rcases hincg'.eq_or_eq_of_isLink hcyc.isLink with rfl | rfl
          · exact mem_walkVertices_self
          · exact hcyc.isPath.target_mem_walkVertices
        · exact mem_walkVertices_of_mem_covered ⟨g', h, hincg'⟩
      rcases eq_or_ne z a with rfl | hza
      · exact Set.mem_insert _ _
      rcases eq_or_ne z b with rfl | hzb
      · exact Set.mem_insert_of_mem _ rfl
      exact absurd hzD (hcc.interior z hzR' hza hzb)
    · rintro z (rfl | rfl)
      · exact ⟨hParc.left_mem, hcut z hcc.mem_left⟩
      · exact ⟨hParc.right_mem, hcut z hcc.mem_right⟩
  
  
  have hxP : x ∉ edgesCover drawing R := fun hxR =>
    hxext (edgesCover_subset_pointSet (fun g hg => hcc.isPath.edge_mem hg) hxR)
  have hmain := crosscut_inside_at_least_one hJcurve hJpoly hPpoly hA1 hA2 hunion hParc hPJ
    hin hxP
  
  have hc₁ : edgesCover drawing (e₁ :: T₁) = edgesCover drawing D₁ ∪ edgesCover drawing R := by
    rw [edgesCover_perm hp₁, edgesCover_append]
  have hc₂ : edgesCover drawing (e₂ :: T₂) = edgesCover drawing D₂ ∪ edgesCover drawing R := by
    rw [edgesCover_perm hp₂, edgesCover_append]
  rw [hc₁, hc₂]
  exact hmain

 









namespace IsPlaneChain

variable {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {n : ℕ} {x : Plane}

 



theorem descent_of_crosscutOff (h : IsPlaneChain Γ drawing G n)
    (hout : OuterOnPairs Γ drawing n x) (hce : CrosscutExists Γ drawing n x)
    (hcen : CrosscutEnclosesOff drawing x) : Descent Γ drawing n x := by
  have hext : x ∈ exterior (chainUnion Γ 0 n) drawing := h.mem_exterior_chain hout
  intro i m him e u v D hcyc hin hA hB
  
  have hblock : chainUnion Γ i (m + 2) ≤ chainUnion Γ 0 n :=
    chainUnion_le fun p _ hp' =>
      h.le_block (i := 0) (m := n) (by omega) (Nat.zero_le p) (by omega)
  have hxb : x ∈ exterior (chainUnion Γ i (m + 2)) drawing :=
    fun hx => hext (pointSet_mono hblock hx)
  obtain ⟨a, b, R, D₁, D₂, hcc⟩ := hce i m him e u v D hcyc hin hA hB
  obtain ⟨e₁, e₂, u₁, v₁, u₂, v₂, T₁, T₂, hc₁, hc₂, hp₁, hp₂⟩ := exists_spliced_cycles hcyc hcc
  exact exists_cycle_edgesOutside_lt hcyc hcc.split.symm hcc.edges_mem hcc.outside₁ hcc.outside₂
    hc₁ hc₂ hp₁ hp₂
    (hcen _ _ (h.block_finite him) (h.block_isDrawing him) (h.block_polygonal him) hxb
      e u v a b D R D₁ D₂ hcyc hcc hin e₁ e₂ u₁ v₁ u₂ v₂ T₁ T₂ hc₁ hc₂ hp₁ hp₂)

 





theorem outer_chain_of_crosscutExists (h : IsPlaneChain Γ drawing G n)
    (hout : OuterOnPairs Γ drawing n x) (hce : CrosscutExists Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing ∧
      ¬ IsBounded (face (chainUnion Γ 0 n) drawing x) :=
  h.outer_chain hout (h.descent_of_crosscutOff hout hce (crosscutEnclosesOff drawing x))

end IsPlaneChain

end Graph
