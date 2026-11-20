/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/OuterChain.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.FaceCyclesLand
import FiniteAvalanches.Support.Schoenflies.Graph.TwoConnected

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




























































































open Set Schoenflies
open scoped Graph

namespace Graph

 

section General

variable {α β : Type*} {Γ : ℕ → Graph α β} {G K : Graph α β} {i m p : ℕ}

 




def chainUnion (Γ : ℕ → Graph α β) (i : ℕ) : ℕ → Graph α β
  | 0 => Γ i
  | m + 1 => (chainUnion Γ i m).union (Γ (i + m + 1))

@[simp]
theorem chainUnion_zero (Γ : ℕ → Graph α β) (i : ℕ) : chainUnion Γ i 0 = Γ i := rfl

@[simp]
theorem chainUnion_succ (Γ : ℕ → Graph α β) (i m : ℕ) :
    chainUnion Γ i (m + 1) = (chainUnion Γ i m).union (Γ (i + m + 1)) := rfl

 
theorem chainUnion_one (Γ : ℕ → Graph α β) (i : ℕ) :
    chainUnion Γ i 1 = (Γ i).union (Γ (i + 1)) := rfl

theorem mem_vertexSet_chainUnion {x : α} :
    x ∈ V(chainUnion Γ i m) ↔ ∃ p, i ≤ p ∧ p ≤ i + m ∧ x ∈ V(Γ p) := by
  induction m with
  | zero =>
    refine ⟨fun h => ⟨i, le_rfl, by omega, h⟩, ?_⟩
    rintro ⟨p, hp, hp', hx⟩
    obtain rfl : p = i := by omega
    exact hx
  | succ m ih =>
    rw [chainUnion_succ, vertexSet_union, Set.mem_union, ih]
    constructor
    · rintro (⟨p, hp, hp', hx⟩ | hx)
      · exact ⟨p, hp, by omega, hx⟩
      · exact ⟨i + m + 1, by omega, by omega, hx⟩
    · rintro ⟨p, hp, hp', hx⟩
      rcases Nat.lt_or_ge p (i + m + 1) with h | h
      · exact Or.inl ⟨p, hp, by omega, hx⟩
      · obtain rfl : p = i + m + 1 := by omega
        exact Or.inr hx

theorem mem_edgeSet_chainUnion {e : β} :
    e ∈ E(chainUnion Γ i m) ↔ ∃ p, i ≤ p ∧ p ≤ i + m ∧ e ∈ E(Γ p) := by
  induction m with
  | zero =>
    refine ⟨fun h => ⟨i, le_rfl, by omega, h⟩, ?_⟩
    rintro ⟨p, hp, hp', he⟩
    obtain rfl : p = i := by omega
    exact he
  | succ m ih =>
    rw [chainUnion_succ, edgeSet_union, Set.mem_union, ih]
    constructor
    · rintro (⟨p, hp, hp', he⟩ | he)
      · exact ⟨p, hp, by omega, he⟩
      · exact ⟨i + m + 1, by omega, by omega, he⟩
    · rintro ⟨p, hp, hp', he⟩
      rcases Nat.lt_or_ge p (i + m + 1) with h | h
      · exact Or.inl ⟨p, hp, by omega, he⟩
      · obtain rfl : p = i + m + 1 := by omega
        exact Or.inr he

 
theorem chainUnion_le (h : ∀ p, i ≤ p → p ≤ i + m → Γ p ≤ G) : chainUnion Γ i m ≤ G := by
  induction m with
  | zero => exact h i le_rfl le_rfl
  | succ m ih =>
    exact union_le (ih fun p hp hp' => h p hp (by omega)) (h (i + m + 1) (by omega) le_rfl)

 


theorem le_chainUnion (hle : ∀ q, i ≤ q → q ≤ i + m → Γ q ≤ G) (hp : i ≤ p) (hp' : p ≤ i + m) :
    Γ p ≤ chainUnion Γ i m := by
  induction m with
  | zero =>
    obtain rfl : p = i := by omega
    exact le_rfl
  | succ m ih =>
    rcases Nat.lt_or_ge p (i + m + 1) with h | h
    · exact (ih (fun q hq hq' => hle q hq (by omega)) (by omega)).trans (left_le_union _ _)
    · obtain rfl : p = i + m + 1 := by omega
      have hcompat : (chainUnion Γ i m).Compatible (Γ (i + m + 1)) :=
        Compatible.of_le_le (chainUnion_le fun q hq hq' => hle q hq (by omega))
          (hle _ (by omega) le_rfl)
      exact hcompat.right_le_union

 
theorem chainUnion_finite (h : ∀ p, i ≤ p → p ≤ i + m → (Γ p).Finite) :
    (chainUnion Γ i m).Finite := by
  induction m with
  | zero => exact h i le_rfl le_rfl
  | succ m ih =>
    have h1 := ih fun p hp hp' => h p hp (by omega)
    have h2 := h (i + m + 1) (by omega) le_rfl
    exact { finite_vertexSet := by
              rw [chainUnion_succ, vertexSet_union]
              exact h1.finite_vertexSet.union h2.finite_vertexSet
            finite_edgeSet := by
              rw [chainUnion_succ, edgeSet_union]
              exact h1.finite_edgeSet.union h2.finite_edgeSet }

 

theorem chainUnion_isTwoConnected (hle : ∀ q, i ≤ q → q ≤ i + m → Γ q ≤ G)
    (htc : ∀ q, i ≤ q → q ≤ i + m → (Γ q).IsTwoConnected)
    (hmeet : ∀ q, i ≤ q → q < i + m → ∃ a b : α, a ≠ b ∧ a ∈ V(Γ q) ∧ a ∈ V(Γ (q + 1)) ∧
      b ∈ V(Γ q) ∧ b ∈ V(Γ (q + 1))) :
    (chainUnion Γ i m).IsTwoConnected := by
  induction m with
  | zero => exact htc i le_rfl le_rfl
  | succ m ih =>
    have hle' : ∀ q, i ≤ q → q ≤ i + m → Γ q ≤ G := fun q hq hq' => hle q hq (by omega)
    have hih := ih hle' (fun q hq hq' => htc q hq (by omega))
      (fun q hq hq' => hmeet q hq (by omega))
    obtain ⟨a, b, hab, haq, haq', hbq, hbq'⟩ := hmeet (i + m) (by omega) (by omega)
    have hsub : Γ (i + m) ≤ chainUnion Γ i m := le_chainUnion hle' (by omega) le_rfl
    have hcompat : (chainUnion Γ i m).Compatible (Γ (i + m + 1)) :=
      Compatible.of_le_le (chainUnion_le hle') (hle _ (by omega) le_rfl)
    exact hih.union hcompat (htc _ (by omega) le_rfl) hab (hsub.vertexSet_mono haq) haq'
      (hsub.vertexSet_mono hbq) hbq'

 




 
theorem IsCycleThrough.mem_edgeSet_cons {e g : β} {u v : α} {D : List β}
    (h : G.IsCycleThrough e u v D) (hg : g ∈ e :: D) : g ∈ E(G) := by
  rcases List.mem_cons.1 hg with rfl | hg
  · exact h.isLink.edge_mem
  · exact h.isPath.edge_mem hg

 
theorem IsCycleThrough.anti {e : β} {u v : α} {D : List β} (h : G.IsCycleThrough e u v D)
    (hKG : K ≤ G) (hE : ∀ g ∈ e :: D, g ∈ E(K)) : K.IsCycleThrough e u v D := by
  have he : e ∈ E(K) := hE e List.mem_cons_self
  have hl : K.IsLink e u v := (hKG.isLink_iff he).2 h.isLink
  exact ⟨hl, h.isPath.anti hKG hl.left_mem fun g hg => hE g (List.mem_cons_of_mem _ hg),
    h.notMem⟩

 
theorem IsCycleThrough.mono {e : β} {u v : α} {D : List β} (h : K.IsCycleThrough e u v D)
    (hKG : K ≤ G) : G.IsCycleThrough e u v D :=
  ⟨h.isLink.mono hKG, h.isPath.mono hKG, h.notMem⟩

 








 


structure IsCycleCrosscut (H F : Graph α β) (e : β) (u v : α) (D : List β) (a b : α)
    (R D₁ D₂ : List β) : Prop where
   
  ne : a ≠ b
   
  arc₁ : H.IsPath a D₁ b
   
  arc₂ : H.IsPath b D₂ a
   
  split : (D₁ ++ D₂).Perm (e :: D)
   
  isPath : H.IsPath a R b
   
  mem_left : a ∈ H.walkVertices u D
   
  mem_right : b ∈ H.walkVertices u D
   
  edges_mem : ∀ g ∈ R, g ∈ E(F)
   
  edges_new : ∀ g ∈ R, g ∉ D ++ [e]
   
  interior : ∀ y ∈ H.walkVertices a R, y ≠ a → y ≠ b → y ∉ H.walkVertices u D
   
  outside₁ : ∃ g ∈ D₁, g ∉ E(F)
   
  outside₂ : ∃ g ∈ D₂, g ∉ E(F)

 


theorem exists_spliced_cycles {H F : Graph α β} {e : β} {u v a b : α} {D R D₁ D₂ : List β}
    (hcyc : H.IsCycleThrough e u v D) (hcc : IsCycleCrosscut H F e u v D a b R D₁ D₂) :
    ∃ (e₁ e₂ : β) (u₁ v₁ u₂ v₂ : α) (T₁ T₂ : List β),
      H.IsCycleThrough e₁ u₁ v₁ T₁ ∧ H.IsCycleThrough e₂ u₂ v₂ T₂ ∧
        (e₁ :: T₁).Perm (D₁ ++ R) ∧ (e₂ :: T₂).Perm (D₂ ++ R) := by
  have hBle : H.cycleGraph u e D ≤ H := hcyc.cycleGraph_le
  have haB : a ∈ V(H.cycleGraph u e D) := by
    rw [hcyc.cycleGraph_vertexSet]; exact hcc.mem_left
  
  have harc : ∀ {W : List β}, (∀ g ∈ W, g ∈ D₁ ++ D₂) →
      ∀ g ∈ W, g ∈ E(H.cycleGraph u e D) := by
    intro W hW g hg
    rw [hcyc.cycleGraph_edgeSet, Set.mem_setOf_eq, List.mem_append]
    rcases List.mem_cons.1 (hcc.split.mem_iff.1 (hW g hg)) with rfl | h
    · exact Or.inr (List.mem_singleton_self _)
    · exact Or.inl h
  have hnew : ∀ g ∈ R, g ∉ E(H.cycleGraph u e D) := by
    intro g hg hmem
    rw [hcyc.cycleGraph_edgeSet, Set.mem_setOf_eq] at hmem
    exact hcc.edges_new g hg hmem
  have hint : ∀ y ∈ H.walkVertices a R, y ≠ a → y ≠ b → y ∉ V(H.cycleGraph u e D) := by
    intro y hy hya hyb
    rw [hcyc.cycleGraph_vertexSet]
    exact hcc.interior y hy hya hyb
  have hHle : (H.cycleGraph u e D).union (H.pathGraphOf a R) ≤ H :=
    union_le hBle (pathGraphOf_le hcc.isPath.isWalk)
  
  obtain ⟨f₁, x₁, y₁, T₁, hc₁, hp₁⟩ :=
    exists_spliced_cycle hBle
      (hcc.arc₁.anti hBle haB (harc fun g hg => List.mem_append_left _ hg))
      hcc.isPath hcc.ne hnew hint
  
  obtain ⟨f₂, x₂, y₂, T₂, hc₂, hp₂⟩ :=
    exists_spliced_cycle hBle
      (hcc.arc₂.reverse.anti hBle haB
        (harc fun g hg => List.mem_append_right _ (List.mem_reverse.1 hg)))
      hcc.isPath hcc.ne hnew hint
  exact ⟨f₁, f₂, x₁, y₁, x₂, y₂, T₁, T₂, hc₁.mono hHle, hc₂.mono hHle, hp₁,
    hp₂.trans ((List.reverse_perm D₂).append_right R)⟩

 

def edgesOutside (H : Graph α β) (W : List β) : Set β := {g | g ∈ W ∧ g ∉ E(H)}

theorem mem_edgesOutside {H : Graph α β} {W : List β} {g : β} :
    g ∈ edgesOutside H W ↔ g ∈ W ∧ g ∉ E(H) := Iff.rfl

theorem finite_edgesOutside (H : Graph α β) (W : List β) : (edgesOutside H W).Finite :=
  (W.finite_toSet).subset fun _ hg => hg.1

theorem edgesOutside_append (H : Graph α β) (W₁ W₂ : List β) :
    edgesOutside H (W₁ ++ W₂) = edgesOutside H W₁ ∪ edgesOutside H W₂ := by
  ext g
  simp only [mem_edgesOutside, List.mem_append, Set.mem_union]
  tauto

theorem edgesOutside_perm {H : Graph α β} {W₁ W₂ : List β} (hp : W₁.Perm W₂) :
    edgesOutside H W₁ = edgesOutside H W₂ := by
  ext g
  simp only [mem_edgesOutside, hp.mem_iff]

theorem edgesOutside_eq_empty {H : Graph α β} {W : List β} (h : ∀ g ∈ W, g ∈ E(H)) :
    edgesOutside H W = ∅ := by
  ext g
  simp only [mem_edgesOutside, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  exact h g

 







theorem edgesOutside_splice_lt {H : Graph α β} {W W' D₁ D₂ R : List β} (hnodup : W.Nodup)
    (hperm : W.Perm (D₁ ++ D₂)) (hperm' : W'.Perm (D₁ ++ R)) (hR : ∀ g ∈ R, g ∈ E(H))
    (hD₂ : ∃ g ∈ D₂, g ∉ E(H)) :
    (edgesOutside H W').ncard < (edgesOutside H W).ncard := by
  obtain ⟨g, hgD₂, hgH⟩ := hD₂
  have hdisj : List.Disjoint D₁ D₂ :=
    List.disjoint_of_nodup_append ((List.Perm.nodup_iff hperm).1 hnodup)
  have hW' : edgesOutside H W' = edgesOutside H D₁ := by
    rw [edgesOutside_perm hperm', edgesOutside_append, edgesOutside_eq_empty hR,
      Set.union_empty]
  have hW : edgesOutside H W = edgesOutside H D₁ ∪ edgesOutside H D₂ := by
    rw [edgesOutside_perm hperm, edgesOutside_append]
  have hsub : edgesOutside H W' ⊆ edgesOutside H W := by
    rw [hW', hW]; exact Set.subset_union_left
  refine Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).2 ⟨g, ?_, ?_⟩)
    (finite_edgesOutside H W)
  · rw [hW]; exact Or.inr ⟨hgD₂, hgH⟩
  · rw [hW']
    exact fun hg' => hdisj hg'.1 hgD₂

end General

 

section Plane

variable {β : Type*} {H K : Graph Plane β} {drawing : β → ℝ → Plane} {x : Plane}

 

def Encloses (H : Graph Plane β) (drawing : β → ℝ → Plane) (x : Plane) : Prop :=
  ∃ (e : β) (u v : Plane) (D : List β),
    H.IsCycleThrough e u v D ∧ x ∈ inside (edgesCover drawing (e :: D))

 
theorem Encloses.mono (hHK : H ≤ K) (h : Encloses H drawing x) : Encloses K drawing x := by
  obtain ⟨e, u, v, D, hc, hin⟩ := h
  exact ⟨e, u, v, D, ⟨hc.isLink.mono hHK, hc.isPath.mono hHK, hc.notMem⟩, hin⟩

 

theorem isBounded_face_of_encloses (hx : x ∈ exterior H drawing)
    (henc : Encloses H drawing x) : Bornology.IsBounded (face H drawing x) := by
  obtain ⟨e, u, v, D, hcyc, hin⟩ := henc
  have hsub : edgesCover drawing (e :: D) ⊆ pointSet H drawing :=
    edgesCover_subset_pointSet fun g hg => hcyc.mem_edgeSet_cons hg
  
  
  have h1 : face H drawing x ⊆ connectedComponentIn (edgesCover drawing (e :: D))ᶜ x :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_face hx) fun w hw hw' => (face_subset_exterior _ _ _ hw) (hsub hw')
  exact (mem_inside_iff.1 hin).2.subset h1

 

theorem encloses_of_isBounded_face [H.Finite] (hd : IsDrawing H drawing)
    (hpoly : ∀ g ∈ E(H), IsPolygonal (edgeArc drawing g)) (h2 : H.IsTwoConnected)
    (hx : x ∈ exterior H drawing) (hb : Bornology.IsBounded (face H drawing x)) :
    Encloses H drawing x := by
  obtain ⟨e, u, v, D, hfc⟩ := face_cycles' hd hpoly h2 x hx
  exact ⟨e, u, v, D, hfc.isCycle, hfc.eq_inside_of_isBounded' hb ▸ mem_face hx⟩

 










theorem exists_cycle_edgesOutside_lt {H F : Graph Plane β} {e : β} {u v : Plane} {D : List β}
    (hcyc : H.IsCycleThrough e u v D) {D₁ D₂ R : List β} (hperm : (e :: D).Perm (D₁ ++ D₂))
    (hR : ∀ g ∈ R, g ∈ E(F)) (h₁ : ∃ g ∈ D₁, g ∉ E(F)) (h₂ : ∃ g ∈ D₂, g ∉ E(F))
    {e₁ e₂ : β} {u₁ v₁ u₂ v₂ : Plane} {T₁ T₂ : List β}
    (hZ₁ : H.IsCycleThrough e₁ u₁ v₁ T₁) (hZ₂ : H.IsCycleThrough e₂ u₂ v₂ T₂)
    (hp₁ : (e₁ :: T₁).Perm (D₁ ++ R)) (hp₂ : (e₂ :: T₂).Perm (D₂ ++ R))
    (hone : x ∈ inside (edgesCover drawing (e₁ :: T₁)) ∨
      x ∈ inside (edgesCover drawing (e₂ :: T₂))) :
    ∃ (e' : β) (u' v' : Plane) (D' : List β), H.IsCycleThrough e' u' v' D' ∧
      x ∈ inside (edgesCover drawing (e' :: D')) ∧
      (edgesOutside F (e' :: D')).ncard < (edgesOutside F (e :: D)).ncard := by
  
  have hnodup : (e :: D).Nodup := List.nodup_cons.2 ⟨hcyc.notMem, hcyc.isPath.nodup⟩
  rcases hone with hx | hx
  · exact ⟨e₁, u₁, v₁, T₁, hZ₁, hx, edgesOutside_splice_lt hnodup hperm hp₁ hR h₂⟩
  · exact ⟨e₂, u₂, v₂, T₂, hZ₂, hx,
      edgesOutside_splice_lt hnodup (hperm.trans List.perm_append_comm) hp₂ hR h₁⟩

end Plane

 

section Chain

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {n : ℕ} {x : Plane}

 




structure IsPlaneChain (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (G : Graph Plane β)
    (n : ℕ) : Prop where
   
  two_le : 2 ≤ n
   
  le_ambient : ∀ p ≤ n, Γ p ≤ G
   
  isDrawing : IsDrawing G drawing
   
  polygonal : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)
   
  finite : ∀ p ≤ n, (Γ p).Finite
   
  twoConnected : ∀ p ≤ n, (Γ p).IsTwoConnected
   
  meet : ∀ p, p + 1 ≤ n → ∃ a b : Plane, a ≠ b ∧ a ∈ V(Γ p) ∧ a ∈ V(Γ (p + 1)) ∧
      b ∈ V(Γ p) ∧ b ∈ V(Γ (p + 1))
   

  disjoint : ∀ p q, p ≤ n → q ≤ n → p + 1 < q →
      Disjoint (pointSet (Γ p) drawing) (pointSet (Γ q) drawing)

namespace IsPlaneChain

variable {i m p : ℕ}

theorem block_le (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) : chainUnion Γ i m ≤ G :=
  chainUnion_le fun p _ hp' => h.le_ambient p (by omega)

theorem le_block (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) (hp : i ≤ p)
    (hp' : p ≤ i + m) : Γ p ≤ chainUnion Γ i m :=
  le_chainUnion (G := G) (fun q _ hq' => h.le_ambient q (by omega)) hp hp'

theorem block_finite (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    (chainUnion Γ i m).Finite :=
  chainUnion_finite fun p _ hp' => h.finite p (by omega)

theorem block_isDrawing (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    IsDrawing (chainUnion Γ i m) drawing :=
  h.isDrawing.mono (h.block_le hm)

theorem block_polygonal (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    ∀ g ∈ E(chainUnion Γ i m), IsPolygonal (edgeArc drawing g) :=
  fun g hg => h.polygonal g ((h.block_le hm).edgeSet_mono hg)

theorem block_isTwoConnected (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    (chainUnion Γ i m).IsTwoConnected :=
  chainUnion_isTwoConnected (G := G) (fun q _ hq' => h.le_ambient q (by omega))
    (fun q _ hq' => h.twoConnected q (by omega)) fun q _ hq' => h.meet q (by omega)

 
theorem mem_pointSet_block {z : Plane} (hz : z ∈ pointSet (chainUnion Γ i m) drawing) :
    ∃ p, i ≤ p ∧ p ≤ i + m ∧ z ∈ pointSet (Γ p) drawing := by
  induction m with
  | zero => exact ⟨i, le_rfl, le_rfl, hz⟩
  | succ m ih =>
    rw [chainUnion_succ, pointSet_union, Set.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨p, hp, hp', hzp⟩ := ih hz
      exact ⟨p, hp, by omega, hzp⟩
    · exact ⟨i + m + 1, by omega, by omega, hz⟩

 


theorem disjoint_block_far (h : IsPlaneChain Γ drawing G n) (hm : i + m + 2 ≤ n) :
    Disjoint (pointSet (chainUnion Γ i m) drawing) (pointSet (Γ (i + m + 2)) drawing) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨q, -, hq', hzq⟩ := mem_pointSet_block hz
  exact Set.disjoint_left.1 (h.disjoint q (i + m + 2) (by omega) (by omega) (by omega)) hzq hz'

 
theorem disjoint_vertexSet (h : IsPlaneChain Γ drawing G n) {q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (hpq : p + 1 < q) : Disjoint V(Γ p) V(Γ q) :=
  (h.disjoint p q hp hq hpq).mono vertexSet_subset_pointSet vertexSet_subset_pointSet

 

theorem disjoint_edgeSet (h : IsPlaneChain Γ drawing G n) {q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (hpq : p + 1 < q) : Disjoint E(Γ p) E(Γ q) := by
  rw [Set.disjoint_left]
  intro g hgp hgq
  have hmem : drawing g 0 ∈ edgeArc drawing g := ⟨0, unitInterval.zero_mem, rfl⟩
  exact Set.disjoint_left.1 (h.disjoint p q hp hq hpq)
    (edgeArc_subset_pointSet hgp hmem) (edgeArc_subset_pointSet hgq hmem)

end IsPlaneChain

 



 



















def Descent (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (n : ℕ) (x : Plane) : Prop :=
  ∀ (i m : ℕ), i + (m + 2) ≤ n →
    ∀ (e : β) (u v : Plane) (D : List β),
      (chainUnion Γ i (m + 2)).IsCycleThrough e u v D →
      x ∈ inside (edgesCover drawing (e :: D)) →
      (∃ g ∈ e :: D, g ∈ E(Γ (i + m + 2)) ∧ g ∉ E(Γ (i + m + 1))) →
      (∃ g ∈ e :: D, g ∈ E(chainUnion Γ i m) ∧ g ∉ E(Γ (i + m + 1))) →
      ∃ (e' : β) (u' v' : Plane) (D' : List β),
        (chainUnion Γ i (m + 2)).IsCycleThrough e' u' v' D' ∧
          x ∈ inside (edgesCover drawing (e' :: D')) ∧
          (edgesOutside (Γ (i + m + 1)) (e' :: D')).ncard <
            (edgesOutside (Γ (i + m + 1)) (e :: D)).ncard

 








 







def CrosscutExists (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (n : ℕ) (x : Plane) :
    Prop :=
  ∀ (i m : ℕ), i + (m + 2) ≤ n →
    ∀ (e : β) (u v : Plane) (D : List β),
      (chainUnion Γ i (m + 2)).IsCycleThrough e u v D →
      x ∈ inside (edgesCover drawing (e :: D)) →
      (∃ g ∈ e :: D, g ∈ E(Γ (i + m + 2)) ∧ g ∉ E(Γ (i + m + 1))) →
      (∃ g ∈ e :: D, g ∈ E(chainUnion Γ i m) ∧ g ∉ E(Γ (i + m + 1))) →
      ∃ (a b : Plane) (R D₁ D₂ : List β),
        IsCycleCrosscut (chainUnion Γ i (m + 2)) (Γ (i + m + 1)) e u v D a b R D₁ D₂

 
















 



def OuterOnPairs (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (n : ℕ) (x : Plane) : Prop :=
  ∀ p, p + 1 ≤ n → x ∈ exterior (chainUnion Γ p 1) drawing ∧
    ¬ Bornology.IsBounded (face (chainUnion Γ p 1) drawing x)

namespace IsPlaneChain

variable {i m p : ℕ}
 

theorem not_encloses_pair (hout : OuterOnPairs Γ drawing n x) (hp : p + 1 ≤ n) :
    ¬ Encloses (chainUnion Γ p 1) drawing x := fun henc =>
  (hout p hp).2 (isBounded_face_of_encloses (hout p hp).1 henc)

 

theorem not_encloses_single (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x)
    (hp : p ≤ n) : ¬ Encloses (Γ p) drawing x := by
  intro henc
  have hn : 2 ≤ n := h.two_le
  rcases Nat.lt_or_ge p n with hlt | hge
  · exact not_encloses_pair hout (by omega)
      (henc.mono (h.le_block (i := p) (m := 1) (by omega) le_rfl (by omega)))
  · 
    obtain ⟨q, hq⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
    obtain rfl : p = q + 1 := by omega
    exact not_encloses_pair hout (by omega)
      (henc.mono (h.le_block (i := q) (m := 1) (by omega) (by omega) (by omega)))

 




theorem not_encloses (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x)
    (hdesc : Descent Γ drawing n x) :
    ∀ m i, i + m ≤ n → ¬ Encloses (chainUnion Γ i m) drawing x := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => exact fun i him => h.not_encloses_single hout (by omega)
    | 1 => exact fun i him => not_encloses_pair hout (by omega)
    | (m + 2) =>
      intro i him henc
      
      
      have inner : ∀ c (e : β) (u v : Plane) (D : List β),
          (chainUnion Γ i (m + 2)).IsCycleThrough e u v D →
          x ∈ inside (edgesCover drawing (e :: D)) →
          (edgesOutside (Γ (i + m + 1)) (e :: D)).ncard < c → False := by
        intro c
        induction c with
        | zero => exact fun _ _ _ _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)
        | succ c ihc =>
          intro e u v D hcyc hin hlt
          
          have hmem : ∀ g ∈ e :: D, ∃ q, i ≤ q ∧ q ≤ i + (m + 2) ∧ g ∈ E(Γ q) := fun g hg =>
            mem_edgeSet_chainUnion.1 (hcyc.mem_edgeSet_cons hg)
          
          
          have hA : ∃ g ∈ e :: D, g ∈ E(Γ (i + m + 2)) ∧ g ∉ E(Γ (i + m + 1)) := by
            by_contra hcon
            push Not at hcon
            have hE : ∀ g ∈ e :: D, g ∈ E(chainUnion Γ i (m + 1)) := by
              intro g hg
              obtain ⟨q, hq, hq', hgq⟩ := hmem g hg
              rcases Nat.lt_or_ge q (i + m + 2) with hlt' | hge'
              · exact mem_edgeSet_chainUnion.2 ⟨q, hq, by omega, hgq⟩
              · obtain rfl : q = i + m + 2 := by omega
                exact mem_edgeSet_chainUnion.2
                  ⟨i + m + 1, by omega, by omega, hcon g hg hgq⟩
            exact ih (m + 1) (by omega) i (by omega)
              ⟨e, u, v, D, hcyc.anti (left_le_union _ _) hE, hin⟩
          
          
          have hB : ∃ g ∈ e :: D, g ∈ E(chainUnion Γ i m) ∧ g ∉ E(Γ (i + m + 1)) := by
            by_contra hcon
            push Not at hcon
            have hpair : chainUnion Γ (i + m + 1) 1 ≤ chainUnion Γ i (m + 2) :=
              chainUnion_le fun q hq hq' =>
                h.le_block him (by omega) (by omega)
            have hE : ∀ g ∈ e :: D, g ∈ E(chainUnion Γ (i + m + 1) 1) := by
              intro g hg
              obtain ⟨q, hq, hq', hgq⟩ := hmem g hg
              rcases Nat.lt_or_ge q (i + m + 1) with hlt' | hge'
              · exact mem_edgeSet_chainUnion.2 ⟨i + m + 1, by omega, by omega,
                  hcon g hg (mem_edgeSet_chainUnion.2 ⟨q, hq, by omega, hgq⟩)⟩
              · exact mem_edgeSet_chainUnion.2 ⟨q, by omega, by omega, hgq⟩
            exact ih 1 (by omega) (i + m + 1) (by omega)
              ⟨e, u, v, D, hcyc.anti hpair hE, hin⟩
          
          obtain ⟨e', u', v', D', hcyc', hin', hlt'⟩ := hdesc i m him e u v D hcyc hin hA hB
          exact ihc e' u' v' D' hcyc' hin' (by omega)
      obtain ⟨e, u, v, D, hcyc, hin⟩ := henc
      exact inner _ e u v D hcyc hin (Nat.lt_succ_self _)

 

theorem mem_exterior_chain (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing := by
  intro hx
  have hn : 2 ≤ n := h.two_le
  obtain ⟨p, -, hp, hxp⟩ := mem_pointSet_block hx
  
  have key : ∀ q, q + 1 ≤ n → x ∉ pointSet (Γ q) drawing ∧ x ∉ pointSet (Γ (q + 1)) drawing := by
    intro q hq
    have := (hout q hq).1
    rw [exterior, chainUnion_one, Set.mem_compl_iff, pointSet_union] at this
    exact ⟨fun hc => this (Or.inl hc), fun hc => this (Or.inr hc)⟩
  rcases Nat.lt_or_ge p n with hlt | hge
  · exact (key p (by omega)).1 hxp
  · obtain ⟨q, hq⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
    obtain rfl : p = q + 1 := by omega
    exact (key q (by omega)).2 hxp

 





theorem outer_chain (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x)
    (hdesc : Descent Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing ∧
      ¬ Bornology.IsBounded (face (chainUnion Γ 0 n) drawing x) := by
  have hext := h.mem_exterior_chain hout
  refine ⟨hext, fun hb => ?_⟩
  haveI : (chainUnion Γ 0 n).Finite := h.block_finite (i := 0) (m := n) (by omega)
  exact h.not_encloses hout hdesc n 0 (by omega)
    (encloses_of_isBounded_face (h.block_isDrawing (by omega)) (h.block_polygonal (by omega))
      (h.block_isTwoConnected (by omega)) hext hb)

end IsPlaneChain

end Chain

end Graph
