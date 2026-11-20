/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/SquareCycle.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.ArcComplement
import FiniteAvalanches.Support.Schoenflies.FaceCycles

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 


























































open Metric Set
open scoped Graph

 

namespace Graph

variable {α β : Type*} {G H : Graph α β} {f g : α → ℝ} {u v w x : α} {e : β}
  {W W₁ W₂ : List β}

 


inductive IsIncWalk (G : Graph α β) (f : α → ℝ) : α → List β → α → Prop
   
  | nil {x : α} (hx : x ∈ V(G)) : G.IsIncWalk f x [] x
   
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hf : f u < f w)
      (hW : G.IsIncWalk f w W v) : G.IsIncWalk f u (e :: W) v

namespace IsIncWalk

theorem isWalk (h : G.IsIncWalk f u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl _ _ ih => exact .cons hl ih

 
theorem source_le (h : G.IsIncWalk f u W v) : ∀ x ∈ G.walkVertices u W, f u ≤ f x := by
  induction h with
  | nil hy =>
    intro x hx
    rw [walkVertices_nil, mem_singleton_iff] at hx
    exact le_of_eq (by rw [hx])
  | @cons u w v e W hl hf _ ih =>
    intro x hx
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact le_rfl
    · exact hf.le.trans (ih x hx')

 
theorem le_target (h : G.IsIncWalk f u W v) : ∀ x ∈ G.walkVertices u W, f x ≤ f v := by
  induction h with
  | nil hy =>
    intro x hx
    rw [walkVertices_nil, mem_singleton_iff] at hx
    exact le_of_eq (by rw [hx])
  | @cons u w v e W hl hf hW ih =>
    intro x hx
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact hf.le.trans (ih w mem_walkVertices_self)
    · exact ih x hx'

 

theorem isPath (h : G.IsIncWalk f u W v) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil hx
  | @cons u w v e W hl hf hW ih =>
    refine .cons hl ih fun hmem => ?_
    exact absurd (hW.source_le u hmem) (not_le.2 hf)

theorem mono (hHG : H ≤ G) (h : H.IsIncWalk f u W v) : G.IsIncWalk f u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | cons hl hf _ ih => exact .cons (hl.mono hHG) hf ih

theorem append (h₁ : G.IsIncWalk f u W₁ w) (h₂ : G.IsIncWalk f w W₂ v) :
    G.IsIncWalk f u (W₁ ++ W₂) v := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hl hf _ ih => exact .cons hl hf (ih h₂)

 
theorem congr_walkVertices (h : G.IsIncWalk f u W v)
    (hfg : ∀ x ∈ G.walkVertices u W, f x = g x) : G.IsIncWalk g u W v := by
  induction h with
  | nil hx => exact .nil hx
  | @cons u w v e W hl hf hW ih =>
    refine .cons hl ?_ (ih fun x hx => hfg x (mem_walkVertices_cons_of_mem hl hx))
    rw [← hfg u mem_walkVertices_self,
      ← hfg w (mem_walkVertices_cons_of_mem hl mem_walkVertices_self)]
    exact hf

 

theorem const_add (h : G.IsIncWalk f u W v) (t : ℝ) :
    G.IsIncWalk (fun x => t + f x) u W v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl hf _ ih => exact .cons hl (by linarith) ih

 
theorem eq_nil_of_eq (h : G.IsIncWalk f u W u) : W = [] := h.isPath.eq_nil_of_eq

 


theorem split_last (h : G.IsIncWalk f u W v) (huv : u ≠ v) :
    ∃ (W' : List β) (e : β) (z : α), W = W' ++ [e] ∧ G.IsIncWalk f u W' z ∧
      G.IsLink e z v ∧ f z < f v := by
  induction h with
  | nil hx => exact absurd rfl huv
  | @cons u w v e W hl hf hW ih =>
    by_cases hwv : w = v
    · subst hwv
      obtain rfl : W = [] := hW.eq_nil_of_eq
      exact ⟨[], e, u, by simp, .nil hl.left_mem, hl, hf⟩
    · obtain ⟨W', e', z, rfl, h₁, h₂, h₃⟩ := ih hwv
      exact ⟨e :: W', e', z, by simp, .cons hl hf h₁, h₂, h₃⟩

end IsIncWalk

end Graph

 







namespace Schoenflies

open Plane

variable {a b p : Plane} {E : Set Piece}

 

theorem exists_mem_segment_dist (hab : a ≠ b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ dist a b) :
    ∃ x ∈ segment ℝ a b, dist a x = t := by
  have hd : 0 < dist a b := dist_pos.2 hab
  refine ⟨AffineMap.lineMap a b (t / dist a b), ?_, ?_⟩
  · rw [segment_eq_image_lineMap]
    exact ⟨t / dist a b, ⟨by positivity, by rw [div_le_one hd]; exact ht1⟩, rfl⟩
  · rw [dist_left_lineMap_of_nonneg a b (by positivity)]
    field_simp

 
theorem dist_le_dist_of_mem_segment {x : Plane} (hab : a ≠ b) (hx : x ∈ segment ℝ a b) :
    dist a x ≤ dist a b :=
  (dist_le_of_mem_segment hab (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
    (by rw [dist_self]; exact dist_nonneg) hx).2

 

theorem exists_ordered_ends (a : Plane) (Q : Piece) :
    ∃ u v : Plane, ((u = Q.1 ∧ v = Q.2) ∨ (u = Q.2 ∧ v = Q.1)) ∧ dist a u ≤ dist a v ∧
      segment ℝ u v = Q.seg ∧ openSegment ℝ u v = Q.interior := by
  rcases le_total (dist a Q.1) (dist a Q.2) with h | h
  · exact ⟨Q.1, Q.2, Or.inl ⟨rfl, rfl⟩, h, rfl, rfl⟩
  · exact ⟨Q.2, Q.1, Or.inr ⟨rfl, rfl⟩, h, segment_symm ℝ _ _, openSegment_symm ℝ _ _⟩

 
theorem ne_of_ordered_ends {Q : Piece} {u v : Plane} (hQ : Q.Nondeg)
    (h : (u = Q.1 ∧ v = Q.2) ∨ (u = Q.2 ∧ v = Q.1)) : u ≠ v := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [hQ, fun e => hQ e.symm]

 




structure IsPieceChain (a b p : Plane) (E : Set Piece) : Prop where
   
  finite : E.Finite
   
  nondeg : ∀ Q ∈ E, Q.Nondeg
   
  sub : ∀ Q ∈ E, Q.seg ⊆ segment ℝ p b
   
  memP : p ∈ segment ℝ a b
   
  ends : ∀ Q ∈ E, ∀ z, (z = Q.1 ∨ z = Q.2) → ∀ Q' ∈ E, z ∉ Q'.interior
   
  disj : ∀ Q ∈ E, ∀ Q' ∈ E, Q ≠ Q' → ∀ x, x ∈ Q.interior → x ∉ Q'.interior
   
  cover : ∀ x ∈ segment ℝ p b, x ≠ b → ∃ Q ∈ E, x ∈ Q.seg

namespace IsPieceChain

variable (hC : IsPieceChain a b p E)
include hC

theorem segment_subset : segment ℝ p b ⊆ segment ℝ a b :=
  (convex_segment a b).segment_subset hC.memP (right_mem_segment ℝ a b)

theorem sub_ab : ∀ Q ∈ E, Q.seg ⊆ segment ℝ a b :=
  fun Q hQ => (hC.sub Q hQ).trans hC.segment_subset

 

theorem notMem_interior (hab : a ≠ b) : ∀ Q ∈ E, p ∉ Q.interior := by
  intro Q hQ hmem
  obtain ⟨u, v, hends, huv, -, hint⟩ := exists_ordered_ends a Q
  have hu : u ∈ segment ℝ a b := by
    refine hC.sub_ab Q hQ ?_
    rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  have hv : v ∈ segment ℝ a b := by
    refine hC.sub_ab Q hQ ?_
    rcases hends with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [right_mem_segment ℝ _ _, left_mem_segment ℝ _ _]
  
  have hup : dist a p ≤ dist a u := by
    refine (dist_le_of_mem_segment hab hC.memP (right_mem_segment ℝ a b)
      (dist_le_dist_of_mem_segment hab hC.memP) ?_).1
    refine hC.sub Q hQ ?_
    rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  have := dist_lt_of_mem_openSegment hab hu hv (ne_of_ordered_ends (hC.nondeg Q hQ) hends) huv
    (hint ▸ hmem)
  linarith [this.1]

end IsPieceChain

 










theorem exists_next_piece (hab : a ≠ b) (hfin : E.Finite)
    (hsub : ∀ Q ∈ E, Q.seg ⊆ segment ℝ a b) (hp : p ∈ segment ℝ a b)
    (hpnot : ∀ Q ∈ E, p ∉ Q.interior)
    (hcover : ∀ x ∈ segment ℝ p b, x ≠ b → ∃ Q ∈ E, x ∈ Q.seg) (hpb : p ≠ b) :
    ∃ Q ∈ E, ∃ w, ((p = Q.1 ∧ w = Q.2) ∨ (p = Q.2 ∧ w = Q.1)) ∧ dist a p < dist a w := by
  have hbseg : b ∈ segment ℝ a b := right_mem_segment ℝ a b
  have hpb' : dist a p < dist a b :=
    lt_of_le_of_ne (dist_le_dist_of_mem_segment hab hp)
      fun h => hpb (eq_of_dist_left_eq hab hp hbseg h)
  
  have hendsfin : {z : Plane | ∃ Q ∈ E, z = Q.1 ∨ z = Q.2}.Finite := by
    refine Set.Finite.subset ((hfin.image (fun Q : Piece => Q.1)).union
      (hfin.image (fun Q : Piece => Q.2))) ?_
    rintro z ⟨Q, hQ, rfl | rfl⟩
    exacts [Or.inl ⟨Q, hQ, rfl⟩, Or.inr ⟨Q, hQ, rfl⟩]
  set D : Set ℝ := (fun z => dist a z) '' {z : Plane | ∃ Q ∈ E, z = Q.1 ∨ z = Q.2} ∪
    {dist a b} with hD
  have hDfin : D.Finite := (hendsfin.image _).union (Set.finite_singleton _)
  set D' : Set ℝ := {t ∈ D | dist a p < t} with hD'
  obtain ⟨m, hmD', hmmin⟩ := Set.exists_min_image D' id (hDfin.subset fun _ ht => ht.1)
    ⟨dist a b, Or.inr rfl, hpb'⟩
  have hmlt : dist a p < m := hmD'.2
  have hmle : m ≤ dist a b := hmmin _ ⟨Or.inr rfl, hpb'⟩
  
  obtain ⟨x, hxseg, hxd⟩ := exists_mem_segment_dist hab
    (t := (dist a p + m) / 2) (by linarith [dist_nonneg (x := a) (y := p)]) (by linarith)
  have hxlt : dist a x < m := by rw [hxd]; linarith
  have hxgt : dist a p < dist a x := by rw [hxd]; linarith
  have hxpb : x ∈ segment ℝ p b :=
    mem_segment_of_dist_le hab hp hbseg hxseg hxgt.le (by linarith)
  have hxb : x ≠ b := fun h => by rw [h] at hxlt; linarith
  obtain ⟨Q, hQE, hxQ⟩ := hcover x hxpb hxb
  obtain ⟨u, v, hends, huv, hseg, hint⟩ := exists_ordered_ends a Q
  have humem : u = Q.1 ∨ u = Q.2 := by
    rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [.inl rfl, .inr rfl]
  have hvmem : v = Q.1 ∨ v = Q.2 := by
    rcases hends with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [.inr rfl, .inl rfl]
  have hu : u ∈ segment ℝ a b := by
    refine hsub Q hQE ?_
    rcases humem with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  have hv : v ∈ segment ℝ a b := by
    refine hsub Q hQE ?_
    rcases hvmem with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  obtain ⟨hux, hxv⟩ := dist_le_of_mem_segment hab hu hv huv (hseg ▸ hxQ)
  
  have hulep : dist a u ≤ dist a p := by
    by_contra hcon
    have : dist a u ∈ D' := ⟨Or.inl ⟨u, ⟨Q, hQE, humem⟩, rfl⟩, lt_of_not_ge hcon⟩
    have := hmmin _ this
    simp only [id] at this
    linarith
  
  have hpleu : dist a p ≤ dist a u := by
    by_contra hcon
    exact hpnot Q hQE (hint ▸ mem_openSegment_of_dist_lt hab hu hv hp (lt_of_not_ge hcon)
      (by linarith))
  have hpu : u = p := eq_of_dist_left_eq hab hu hp (le_antisymm hulep hpleu)
  subst hpu
  refine ⟨Q, hQE, v, ?_, by linarith⟩
  rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  exacts [Or.inl ⟨h₁, h₂⟩, Or.inr ⟨h₁, h₂⟩]

 
theorem mem_seg_of_end {Q : Piece} {z : Plane} (h : z = Q.1 ∨ z = Q.2) : z ∈ Q.seg := by
  rcases h with rfl | rfl
  exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]

 






theorem exists_incWalk_of_chain {G : Graph Plane Piece} (hab : a ≠ b) (hbG : b ∈ V(G)) :
    ∀ (n : ℕ) (p : Plane) (E : Set Piece), E.ncard = n → IsPieceChain a b p E →
      (∀ Q ∈ E, G.IsLink Q Q.1 Q.2) →
      ∃ W : List Piece, (∀ Q, Q ∈ W ↔ Q ∈ E) ∧ G.IsIncWalk (fun z => dist a z) p W b := by
  have hbseg : b ∈ segment ℝ a b := right_mem_segment ℝ a b
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p E hcard hC hlink
  by_cases hpb : p = b
  · 
    subst hpb
    have hE : E = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro Q hQ
      have h1 := hC.sub Q hQ
      rw [segment_same] at h1
      exact hC.nondeg Q hQ
        ((h1 (left_mem_segment ℝ Q.1 Q.2)).trans (h1 (right_mem_segment ℝ Q.1 Q.2)).symm)
    exact ⟨[], by simp [hE], .nil hbG⟩
  · obtain ⟨Q, hQE, w, hQw, hlt⟩ := exists_next_piece hab hC.finite hC.sub_ab hC.memP
      (hC.notMem_interior hab) hC.cover hpb
    have hwQ : w = Q.1 ∨ w = Q.2 := by
      rcases hQw with ⟨-, rfl⟩ | ⟨-, rfl⟩
      exacts [.inr rfl, .inl rfl]
    have hpQ : p = Q.1 ∨ p = Q.2 := by
      rcases hQw with ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [.inl rfl, .inr rfl]
    have hQseg : Q.seg = segment ℝ p w := by
      rcases hQw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [rfl, segment_symm ℝ _ _]
    have hQint : Q.interior = openSegment ℝ p w := by
      rcases hQw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [rfl, openSegment_symm ℝ _ _]
    have hlinkQ : G.IsLink Q p w := by
      have := hlink Q hQE
      rcases hQw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [this, this.symm]
    have hwpb : w ∈ segment ℝ p b := hC.sub Q hQE (mem_seg_of_end hwQ)
    have hwab : w ∈ segment ℝ a b := hC.segment_subset hwpb
    have hwsub : segment ℝ w b ⊆ segment ℝ p b :=
      (convex_segment p b).segment_subset hwpb (right_mem_segment ℝ p b)
    
    have hcov' : ∀ x ∈ segment ℝ w b, x ≠ b → ∃ R ∈ E \ {Q}, x ∈ R.seg := by
      intro x hx hxb
      obtain ⟨R, hRE, hxR⟩ := hC.cover x (hwsub hx) hxb
      by_cases hRQ : R = Q
      · 
        subst hRQ
        have hxw : x = w := by
          have h1 : dist a x ≤ dist a w :=
            (dist_le_of_mem_segment hab hC.memP hwab hlt.le (hQseg ▸ hxR)).2
          have h2 : dist a w ≤ dist a x :=
            (dist_le_of_mem_segment hab hwab hbseg
              (dist_le_dist_of_mem_segment hab hwab) hx).1
          exact eq_of_dist_left_eq hab (hC.segment_subset (hwsub hx)) hwab (le_antisymm h1 h2)
        subst hxw
        obtain ⟨R', hR'E, w', hR'w, hlt'⟩ := exists_next_piece hab hC.finite hC.sub_ab hwab
          (fun S hS => hC.ends R hRE x hwQ S hS)
          (fun y hy hyb => hC.cover y (hwsub hy) hyb) hxb
        refine ⟨R', ⟨hR'E, ?_⟩, mem_seg_of_end (by
          rcases hR'w with ⟨h, -⟩ | ⟨h, -⟩
          exacts [.inl h, .inr h])⟩
        
        intro hmem
        rw [Set.mem_singleton_iff] at hmem
        subst hmem
        have : x = p ∨ w' = p := by
          rcases hR'w with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rcases hQw with ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩
          exacts [Or.inl (e₁.trans f₁.symm), Or.inr (e₂.trans f₁.symm),
            Or.inr (e₂.trans f₁.symm), Or.inl (e₁.trans f₁.symm)]
        rcases this with h | h
        · rw [h] at hlt; exact absurd hlt (lt_irrefl _)
        · rw [h] at hlt'; linarith
      · exact ⟨R, ⟨hRE, by simpa using hRQ⟩, hxR⟩
    have hsub' : ∀ R ∈ E \ {Q}, R.seg ⊆ segment ℝ w b := by
      rintro R ⟨hRE, hRQ⟩ y hy
      rw [Set.mem_singleton_iff] at hRQ
      obtain ⟨u, v, hends, huv, hseg, hint⟩ := exists_ordered_ends a R
      have hu : u ∈ segment ℝ a b :=
        hC.sub_ab R hRE (mem_seg_of_end (by
          rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
          exacts [.inl rfl, .inr rfl]))
      have hv : v ∈ segment ℝ a b :=
        hC.sub_ab R hRE (mem_seg_of_end (by
          rcases hends with ⟨-, rfl⟩ | ⟨-, rfl⟩
          exacts [.inr rfl, .inl rfl]))
      have hpu : dist a p ≤ dist a u :=
        (dist_le_of_mem_segment hab hC.memP hbseg (dist_le_dist_of_mem_segment hab hC.memP)
          (hC.sub R hRE (mem_seg_of_end (by
            rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
            exacts [.inl rfl, .inr rfl])))).1
      have huv' : dist a u < dist a v :=
        lt_of_le_of_ne huv fun h =>
          ne_of_ordered_ends (hC.nondeg R hRE) hends (eq_of_dist_left_eq hab hu hv h)
      have hwnot : w ∉ openSegment ℝ u v := hint ▸ hC.ends Q hQE w hwQ R hRE
      have hdi : dist a w ≤ dist a u ∨ dist a v ≤ dist a w := by
        by_contra hcon
        push Not at hcon
        exact hwnot (mem_openSegment_of_dist_lt hab hu hv hwab hcon.1 hcon.2)
      rcases hdi with hdi | hdi
      · obtain ⟨h1, h2⟩ := dist_le_of_mem_segment hab hu hv huv (hseg ▸ hy)
        exact mem_segment_of_dist_le hab hwab hbseg (hC.sub_ab R hRE hy) (hdi.trans h1)
          (h2.trans (dist_le_dist_of_mem_segment hab hv))
      · 
        exfalso
        obtain ⟨y', hy'seg, hy'd⟩ := exists_mem_segment_dist hab
          (t := (dist a u + dist a v) / 2) (by linarith [dist_nonneg (x := a) (y := u)])
          (by linarith [dist_le_dist_of_mem_segment hab hv])
        refine hC.disj R hRE Q hQE hRQ y' ?_ ?_
        · exact hint ▸ mem_openSegment_of_dist_lt hab hu hv hy'seg
            (by rw [hy'd]; linarith) (by rw [hy'd]; linarith)
        · exact hQint ▸ mem_openSegment_of_dist_lt hab hC.memP hwab hy'seg
            (by rw [hy'd]; linarith) (by rw [hy'd]; linarith)
    have hC' : IsPieceChain a b w (E \ {Q}) :=
      { finite := hC.finite.subset Set.sdiff_subset
        nondeg := fun R hR => hC.nondeg R hR.1
        sub := hsub'
        memP := hwab
        ends := fun R hR z hz R' hR' => hC.ends R hR.1 z hz R' hR'.1
        disj := fun R hR R' hR' hne => hC.disj R hR.1 R' hR'.1 hne
        cover := hcov' }
    have hcard' : (E \ {Q}).ncard < n := by
      rw [← hcard]; exact Set.ncard_sdiff_singleton_lt_of_mem hQE hC.finite
    obtain ⟨W, hWmem, hWwalk⟩ :=
      ih _ hcard' w (E \ {Q}) rfl hC' (fun R hR => hlink R hR.1)
    refine ⟨Q :: W, fun R => ?_, .cons hlinkQ hlt hWwalk⟩
    simp only [List.mem_cons, hWmem, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨h, -⟩)
      exacts [hQE, h]
    · intro hR
      by_cases h : R = Q
      · exact Or.inl h
      · exact Or.inr ⟨hR, h⟩

 







variable {c z : Plane} {r : ℝ}

open Plane

 
theorem dist_eq_abs_fst {z w : Plane} (h : z 1 = w 1) : dist z w = |z 0 - w 0| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, h, sub_self,
    abs_zero]
  rw [show |z 0 - w 0| ^ 2 + (0 : ℝ) ^ 2 = |z 0 - w 0| ^ 2 by ring, Real.sqrt_sq_eq_abs,
    abs_abs]

 
theorem dist_eq_abs_snd {z w : Plane} (h : z 0 = w 0) : dist z w = |z 1 - w 1| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, h, sub_self,
    abs_zero]
  rw [show (0 : ℝ) ^ 2 + |z 1 - w 1| ^ 2 = |z 1 - w 1| ^ 2 by ring, Real.sqrt_sq_eq_abs,
    abs_abs]

theorem dist_sqNE_sqNW (c : Plane) (hr : 0 ≤ r) : dist (sqNE c r) (sqNW c r) = 2 * r := by
  rw [dist_eq_abs_fst (by simp)]
  simp only [sqNE_zero, sqNW_zero]
  rw [show c 0 + r - (c 0 - r) = 2 * r by ring, abs_of_nonneg (by linarith)]

theorem dist_sqNW_sqSW (c : Plane) (hr : 0 ≤ r) : dist (sqNW c r) (sqSW c r) = 2 * r := by
  rw [dist_eq_abs_snd (by simp)]
  simp only [sqNW_one, sqSW_one]
  rw [show c 1 + r - (c 1 - r) = 2 * r by ring, abs_of_nonneg (by linarith)]

theorem dist_sqSW_sqSE (c : Plane) (hr : 0 ≤ r) : dist (sqSW c r) (sqSE c r) = 2 * r := by
  rw [dist_eq_abs_fst (by simp)]
  simp only [sqSW_zero, sqSE_zero]
  rw [show c 0 - r - (c 0 + r) = -(2 * r) by ring, abs_neg, abs_of_nonneg (by linarith)]

theorem dist_sqSE_sqNE (c : Plane) (hr : 0 ≤ r) : dist (sqSE c r) (sqNE c r) = 2 * r := by
  rw [dist_eq_abs_snd (by simp)]
  simp only [sqSE_one, sqNE_one]
  rw [show c 1 - r - (c 1 + r) = -(2 * r) by ring, abs_neg, abs_of_nonneg (by linarith)]

 

theorem dist_sqNE_of_mem_top (hr : 0 ≤ r) (hz : z ∈ segment ℝ (sqNE c r) (sqNW c r)) :
    dist (sqNE c r) z = c 0 + r - z 0 := by
  rw [mem_seg_top hr] at hz
  rw [dist_eq_abs_fst (by simp [hz.1]), sqNE_zero,
    abs_of_nonneg (by have := (abs_le.1 hz.2).2; linarith)]

theorem dist_sqNW_of_mem_left (hr : 0 ≤ r) (hz : z ∈ segment ℝ (sqNW c r) (sqSW c r)) :
    dist (sqNW c r) z = c 1 + r - z 1 := by
  rw [mem_seg_left hr] at hz
  rw [dist_eq_abs_snd (by simp [hz.1]), sqNW_one,
    abs_of_nonneg (by have := (abs_le.1 hz.2).2; linarith)]

theorem dist_sqSW_of_mem_bottom (hr : 0 ≤ r) (hz : z ∈ segment ℝ (sqSW c r) (sqSE c r)) :
    dist (sqSW c r) z = z 0 - (c 0 - r) := by
  rw [mem_seg_bottom hr] at hz
  rw [dist_eq_abs_fst (by simp [hz.1]), sqSW_zero, abs_sub_comm,
    abs_of_nonneg (by have := (abs_le.1 hz.2).1; linarith)]

theorem dist_sqSE_of_mem_right (hr : 0 ≤ r) (hz : z ∈ segment ℝ (sqSE c r) (sqNE c r)) :
    dist (sqSE c r) z = z 1 - (c 1 - r) := by
  rw [mem_seg_right hr] at hz
  rw [dist_eq_abs_snd (by simp [hz.1]), sqSE_one, abs_sub_comm,
    abs_of_nonneg (by have := (abs_le.1 hz.2).1; linarith)]

 

theorem eq_sqNW_of_mem_top_left (hr : 0 ≤ r) (h₁ : z ∈ segment ℝ (sqNE c r) (sqNW c r))
    (h₂ : z ∈ segment ℝ (sqNW c r) (sqSW c r)) : z = sqNW c r := by
  rw [mem_seg_top hr] at h₁
  rw [mem_seg_left hr] at h₂
  ext i
  fin_cases i
  exacts [h₂.1, h₁.1]

theorem notMem_top_of_mem_bottom (hr : 0 < r) (h₁ : z ∈ segment ℝ (sqSW c r) (sqSE c r)) :
    z ∉ segment ℝ (sqNE c r) (sqNW c r) := by
  rw [mem_seg_bottom hr.le] at h₁
  rw [mem_seg_top hr.le]
  rintro ⟨h, -⟩
  rw [h₁.1] at h
  linarith

theorem eq_sqNE_of_mem_top_right (hr : 0 ≤ r) (h₁ : z ∈ segment ℝ (sqNE c r) (sqNW c r))
    (h₂ : z ∈ segment ℝ (sqSE c r) (sqNE c r)) : z = sqNE c r := by
  rw [mem_seg_top hr] at h₁
  rw [mem_seg_right hr] at h₂
  ext i
  fin_cases i
  exacts [h₂.1, h₁.1]

theorem eq_sqSW_of_mem_left_bottom (hr : 0 ≤ r) (h₁ : z ∈ segment ℝ (sqNW c r) (sqSW c r))
    (h₂ : z ∈ segment ℝ (sqSW c r) (sqSE c r)) : z = sqSW c r := by
  rw [mem_seg_left hr] at h₁
  rw [mem_seg_bottom hr] at h₂
  ext i
  fin_cases i
  exacts [h₁.1, h₂.1]

theorem notMem_left_of_mem_right (hr : 0 < r) (h₁ : z ∈ segment ℝ (sqSE c r) (sqNE c r)) :
    z ∉ segment ℝ (sqNW c r) (sqSW c r) := by
  rw [mem_seg_right hr.le] at h₁
  rw [mem_seg_left hr.le]
  rintro ⟨h, -⟩
  rw [h₁.1] at h
  linarith

theorem eq_sqSE_of_mem_bottom_right (hr : 0 ≤ r) (h₁ : z ∈ segment ℝ (sqSW c r) (sqSE c r))
    (h₂ : z ∈ segment ℝ (sqSE c r) (sqNE c r)) : z = sqSE c r := by
  rw [mem_seg_bottom hr] at h₁
  rw [mem_seg_right hr] at h₂
  ext i
  fin_cases i
  exacts [h₂.1, h₁.1]

 

open scoped Classical in
 






noncomputable def sqCoord (c : Plane) (r : ℝ) (z : Plane) : ℝ :=
  if z ∈ segment ℝ (sqNE c r) (sqNW c r) then dist (sqNE c r) z
  else if z ∈ segment ℝ (sqNW c r) (sqSW c r) then 2 * r + dist (sqNW c r) z
  else if z ∈ segment ℝ (sqSW c r) (sqSE c r) then 4 * r + dist (sqSW c r) z
  else 6 * r + dist (sqSE c r) z

theorem sqCoord_top (hz : z ∈ segment ℝ (sqNE c r) (sqNW c r)) :
    sqCoord c r z = dist (sqNE c r) z := by
  classical
  rw [sqCoord, if_pos hz]

theorem sqCoord_left (hr : 0 ≤ r) (hz : z ∈ segment ℝ (sqNW c r) (sqSW c r)) :
    sqCoord c r z = 2 * r + dist (sqNW c r) z := by
  classical
  by_cases htop : z ∈ segment ℝ (sqNE c r) (sqNW c r)
  · 
    obtain rfl := eq_sqNW_of_mem_top_left hr htop hz
    rw [sqCoord, if_pos htop, dist_sqNE_sqNW c hr, dist_self, add_zero]
  · rw [sqCoord, if_neg htop, if_pos hz]

theorem sqCoord_bottom (hr : 0 < r) (hz : z ∈ segment ℝ (sqSW c r) (sqSE c r)) :
    sqCoord c r z = 4 * r + dist (sqSW c r) z := by
  classical
  have htop : z ∉ segment ℝ (sqNE c r) (sqNW c r) := notMem_top_of_mem_bottom hr hz
  by_cases hleft : z ∈ segment ℝ (sqNW c r) (sqSW c r)
  · obtain rfl := eq_sqSW_of_mem_left_bottom hr.le hleft hz
    rw [sqCoord, if_neg htop, if_pos hleft, dist_sqNW_sqSW c hr.le, dist_self, add_zero]
    ring
  · rw [sqCoord, if_neg htop, if_neg hleft, if_pos hz]

theorem sqCoord_right (hr : 0 < r) (hz : z ∈ segment ℝ (sqSE c r) (sqNE c r))
    (hne : z ≠ sqNE c r) : sqCoord c r z = 6 * r + dist (sqSE c r) z := by
  classical
  have htop : z ∉ segment ℝ (sqNE c r) (sqNW c r) :=
    fun h => hne (eq_sqNE_of_mem_top_right hr.le h hz)
  have hleft : z ∉ segment ℝ (sqNW c r) (sqSW c r) := notMem_left_of_mem_right hr hz
  by_cases hbot : z ∈ segment ℝ (sqSW c r) (sqSE c r)
  · obtain rfl := eq_sqSE_of_mem_bottom_right hr.le hbot hz
    rw [sqCoord, if_neg htop, if_neg hleft, if_pos hbot, dist_sqSW_sqSE c hr.le, dist_self,
      add_zero]
    ring
  · rw [sqCoord, if_neg htop, if_neg hleft, if_neg hbot]

 







variable {pieces : List Piece} {points : List Plane}

 
def sideEdges (pieces : List Piece) (points : List Plane) (c : Plane) (r : ℝ) (S : Piece) :
    Set Piece := {Q | Q ∈ squareEdges pieces points c r ∧ Q.seg ⊆ S.seg}

 

theorem coord_mem_segment {y u v : Plane} (i : Fin 2) (h : y ∈ segment ℝ u v) :
    y i ∈ segment ℝ (u i) (v i) := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := h
  exact ⟨p, q, hp, hq, hpq, by rw [Plane.smul_add_apply]; simp [smul_eq_mul]⟩

 
theorem abs_le_of_mem_frontier {y : Plane} (hy : y ∈ frontier (closedSquare c r)) :
    |y 0 - c 0| ≤ r ∧ |y 1 - c 1| ≤ r := by
  rw [mem_frontier_closedSquare] at hy
  exact ⟨hy ▸ le_max_left _ _, hy ▸ le_max_right _ _⟩

 
theorem exists_side_of_mem_squareEdges (hr : 0 < r)
    {Q : Piece} (hQ : Q ∈ squareEdges pieces points c r) :
    ∃ S ∈ squarePieces c r, Q ∈ sideEdges pieces points c r S := by
  obtain ⟨hQov, hQfr⟩ := hQ
  
  have h1 := abs_le_of_mem_frontier (hQfr (left_mem_segment ℝ Q.1 Q.2))
  have h2 := abs_le_of_mem_frontier (hQfr (right_mem_segment ℝ Q.1 Q.2))
  have hmseg : (2⁻¹ : ℝ) • Q.1 + (2⁻¹ : ℝ) • Q.2 ∈ Q.seg :=
    ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, rfl⟩
  have hm0 : ((2⁻¹ : ℝ) • Q.1 + (2⁻¹ : ℝ) • Q.2) 0 = (Q.1 0 + Q.2 0) / 2 := by
    rw [Plane.smul_add_apply]; ring
  have hm1 : ((2⁻¹ : ℝ) • Q.1 + (2⁻¹ : ℝ) • Q.2) 1 = (Q.1 1 + Q.2 1) / 2 := by
    rw [Plane.smul_add_apply]; ring
  have hmax : max |(Q.1 0 + Q.2 0) / 2 - c 0| |(Q.1 1 + Q.2 1) / 2 - c 1| = r := by
    have := mem_frontier_closedSquare.1 (hQfr hmseg)
    rwa [hm0, hm1] at this
  
  have key : ∀ (i : Fin 2) (t : ℝ), Q.1 i = t → Q.2 i = t → ∀ y ∈ Q.seg, y i = t := by
    intro i t hu' hv' y hy
    have hc := coord_mem_segment i (show y ∈ segment ℝ Q.1 Q.2 from hy)
    rw [hu', hv', segment_same, mem_singleton_iff] at hc
    exact hc
  simp only [abs_le] at h1 h2
  rcases max_choice |(Q.1 0 + Q.2 0) / 2 - c 0| |(Q.1 1 + Q.2 1) / 2 - c 1| with hch | hch <;>
      rw [hch] at hmax <;> rcases (abs_eq hr.le).1 hmax with heq | heq
  · 
    have e₁ : Q.1 0 = c 0 + r := by linarith [h1.1.2, h2.1.2]
    have e₂ : Q.2 0 = c 0 + r := by linarith [h1.1.2, h2.1.2]
    exact ⟨(sqSE c r, sqNE c r), by simp [squarePieces], ⟨hQov, hQfr⟩, fun y hy =>
      (mem_seg_right hr.le).2 ⟨key 0 (c 0 + r) e₁ e₂ y hy,
        (abs_le_of_mem_frontier (hQfr hy)).2⟩⟩
  · 
    have e₁ : Q.1 0 = c 0 - r := by linarith [h1.1.1, h2.1.1]
    have e₂ : Q.2 0 = c 0 - r := by linarith [h1.1.1, h2.1.1]
    exact ⟨(sqNW c r, sqSW c r), by simp [squarePieces], ⟨hQov, hQfr⟩, fun y hy =>
      (mem_seg_left hr.le).2 ⟨key 0 (c 0 - r) e₁ e₂ y hy,
        (abs_le_of_mem_frontier (hQfr hy)).2⟩⟩
  · 
    have e₁ : Q.1 1 = c 1 + r := by linarith [h1.2.2, h2.2.2]
    have e₂ : Q.2 1 = c 1 + r := by linarith [h1.2.2, h2.2.2]
    exact ⟨(sqNE c r, sqNW c r), by simp [squarePieces], ⟨hQov, hQfr⟩, fun y hy =>
      (mem_seg_top hr.le).2 ⟨key 1 (c 1 + r) e₁ e₂ y hy,
        (abs_le_of_mem_frontier (hQfr hy)).1⟩⟩
  · 
    have e₁ : Q.1 1 = c 1 - r := by linarith [h1.2.1, h2.2.1]
    have e₂ : Q.2 1 = c 1 - r := by linarith [h1.2.1, h2.2.1]
    exact ⟨(sqSW c r, sqSE c r), by simp [squarePieces], ⟨hQov, hQfr⟩, fun y hy =>
      (mem_seg_bottom hr.le).2 ⟨key 1 (c 1 - r) e₁ e₂ y hy,
        (abs_le_of_mem_frontier (hQfr hy)).1⟩⟩

 




theorem mem_vertexSet_squareGraph_iff {y : Plane} :
    y ∈ V(squareGraph pieces points c r) ↔
      ∃ Q ∈ squareEdges pieces points c r, y = Q.1 ∨ y = Q.2 := Iff.rfl

theorem mem_edgeSet_squareGraph_iff {Q : Piece} :
    Q ∈ E(squareGraph pieces points c r) ↔ Q ∈ squareEdges pieces points c r := Iff.rfl

 
theorem inc_of_mem_squareEdges {Q : Piece} {y : Plane}
    (hQ : Q ∈ squareEdges pieces points c r) (hy : y = Q.1 ∨ y = Q.2) :
    (squareGraph pieces points c r).Inc Q y := by
  rcases hy with rfl | rfl
  exacts [⟨Q.2, hQ, Or.inl ⟨rfl, rfl⟩⟩, ⟨Q.1, hQ, Or.inr ⟨rfl, rfl⟩⟩]

 
theorem isLink_of_mem_squareEdges {Q : Piece} (hQ : Q ∈ squareEdges pieces points c r) :
    (squareGraph pieces points c r).IsLink Q Q.1 Q.2 := ⟨hQ, Or.inl ⟨rfl, rfl⟩⟩

 
theorem side_subset_frontier (hr : 0 ≤ r) {S : Piece} (hS : S ∈ squarePieces c r) :
    S.seg ⊆ frontier (closedSquare c r) := by
  rw [← cover_squarePieces c hr]
  exact fun y hy => Set.mem_iUnion₂.2 ⟨S, hS, hy⟩

 





 
def insideEdges (pieces : List Piece) (points : List Plane) (P₀ : Piece) : Set Piece :=
  {Q | Q ∈ overlayPieces pieces points ∧ Q.seg ⊆ P₀.seg}

 


theorem isPieceChain_insideEdges (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points) {P₀ : Piece}
    (hP₀ : P₀ ∈ pieces) : IsPieceChain P₀.1 P₀.2 P₀.1 (insideEdges pieces points P₀) where
  finite := (overlayPieces pieces points).finite_toSet.subset fun _ h => h.1
  nondeg := fun Q hQ => overlayPieces_nondeg points hnd Q hQ.1
  sub := fun Q hQ => hQ.2
  memP := left_mem_segment ℝ P₀.1 P₀.2
  ends := fun Q hQ z hz Q' hQ' =>
    overlayPieces_avoids hnd z (overlayPieces_ends_cut hEnds Q hQ.1 z hz) Q' hQ'.1
  disj := fun Q hQ Q' hQ' hne x hx =>
    overlayPieces_disjoint_interiors hnd hEnds hMeets hQ.1 hQ'.1 hne hx
  cover := by
    intro x hx _
    obtain ⟨Q, hQ, hxQ, hQsub⟩ := exists_overlayPiece_mem_subset (points := points) hP₀ hx
    exact ⟨Q, ⟨hQ, hQsub⟩, hxQ⟩

 


theorem exists_incWalk_insideEdges (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points) {P₀ : Piece}
    (hP₀ : P₀ ∈ pieces) (hP₀nd : P₀.Nondeg) :
    ∃ W : List Piece, (∀ Q, Q ∈ W ↔ Q ∈ insideEdges pieces points P₀) ∧
      (overlayGraph pieces points).IsIncWalk (fun z => dist P₀.1 z) P₀.1 W P₀.2 := by
  
  obtain ⟨Q, hQ, hend, -⟩ := exists_overlayPiece_end_subset (points := points) hnd
    (hEnds P₀ hP₀ P₀.2 (Or.inr rfl)) hP₀ (right_mem_segment ℝ P₀.1 P₀.2)
  exact exists_incWalk_of_chain (G := overlayGraph pieces points) hP₀nd ⟨Q, hQ, hend⟩
    _ P₀.1 _ rfl
    (isPieceChain_insideEdges hnd hEnds hMeets hP₀) fun R hR => ⟨hR.1, Or.inl ⟨rfl, rfl⟩⟩

 
theorem sideEdges_eq_insideEdges (hr : 0 ≤ r) {S : Piece} (hS : S ∈ squarePieces c r) :
    sideEdges pieces points c r S = insideEdges pieces points S := by
  ext Q
  exact ⟨fun h => ⟨h.1.1, h.2⟩,
    fun h => ⟨⟨h.1, h.2.trans (side_subset_frontier hr hS)⟩, h.2⟩⟩

 
theorem isPieceChain_sideEdges (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) (hr : 0 < r)
    (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) {S : Piece} (hS : S ∈ squarePieces c r) :
    IsPieceChain S.1 S.2 S.1 (sideEdges pieces points c r S) :=
  sideEdges_eq_insideEdges (pieces := pieces) (points := points) hr.le hS ▸
    isPieceChain_insideEdges hnd hEnds hMeets (hsub S hS)

 

theorem corner_mem_vertexSet (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hr : 0 < r) (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) {S : Piece}
    (hS : S ∈ squarePieces c r) : S.2 ∈ V(squareGraph pieces points c r) :=
  mem_vertexSet_squareGraph hnd hr.le hsub (hEnds S (hsub S hS) S.2 (Or.inr rfl))
    (side_subset_frontier hr.le hS (right_mem_segment ℝ S.1 S.2))

 

theorem exists_side_walk (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) (hr : 0 < r)
    (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) {u v : Plane}
    (hS : (u, v) ∈ squarePieces c r) :
    ∃ W : List Piece, (∀ Q, Q ∈ W ↔ Q ∈ sideEdges pieces points c r (u, v)) ∧
      (squareGraph pieces points c r).IsIncWalk (fun z => dist u z) u W v :=
  exists_incWalk_of_chain (squarePieces_nondeg c hr _ hS)
    (corner_mem_vertexSet hnd hEnds hr hsub hS) _ u _ rfl
    (isPieceChain_sideEdges hnd hEnds hMeets hr hsub hS)
    fun _ hQ => isLink_of_mem_squareEdges hQ.1

 
theorem walkVertices_squareGraph_subset {u : Plane} {W : List Piece} {T : Set Plane}
    (hu : u ∈ T) (hW : ∀ Q ∈ W, Q.seg ⊆ T) :
    (squareGraph pieces points c r).walkVertices u W ⊆ T := by
  rintro x hx
  rcases Graph.mem_walkVertices_iff.1 hx with rfl | ⟨Q, hQ, y, hy⟩
  · exact hu
  · refine hW Q hQ (mem_seg_of_end ?_)
    rcases hy.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [Or.inl rfl, Or.inr rfl]

 
theorem not_nondeg_of_seg_subset_singleton {Q : Piece} {t : Plane} (h : ∀ y ∈ Q.seg, y = t) :
    ¬ Q.Nondeg := fun hne =>
  hne ((h Q.1 (left_mem_segment ℝ _ _)).trans (h Q.2 (right_mem_segment ℝ _ _)).symm)

 






theorem sqNW_ne_sqNE (c : Plane) (hr : 0 < r) : sqNW c r ≠ sqNE c r := by
  intro h
  have h0 := congrArg (fun p : Plane => p 0) h
  simp only [sqNW_zero, sqNE_zero] at h0
  linarith

theorem sqSE_ne_sqNE (c : Plane) (hr : 0 < r) : sqSE c r ≠ sqNE c r := by
  intro h
  have h1 := congrArg (fun p : Plane => p 1) h
  simp only [sqSE_one, sqNE_one] at h1
  linarith

 



theorem exists_isLongCycle_squareGraph (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points) (hr : 0 < r)
    (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) :
    ∃ (e : Piece) (u v : Plane) (D : List Piece) (w : Plane),
      (squareGraph pieces points c r).IsLongCycle e u v D w ∧
        (squareGraph pieces points c r).cycleGraph u e D = squareGraph pieces points c r := by
  set K := squareGraph pieces points c r with hKdef
  have hS₁ : (sqNE c r, sqNW c r) ∈ squarePieces c r := by simp [squarePieces]
  have hS₂ : (sqNW c r, sqSW c r) ∈ squarePieces c r := by simp [squarePieces]
  have hS₃ : (sqSW c r, sqSE c r) ∈ squarePieces c r := by simp [squarePieces]
  have hS₄ : (sqSE c r, sqNE c r) ∈ squarePieces c r := by simp [squarePieces]
  obtain ⟨W₁, hm₁, hw₁⟩ := exists_side_walk hnd hEnds hMeets hr hsub hS₁
  obtain ⟨W₂, hm₂, hw₂⟩ := exists_side_walk hnd hEnds hMeets hr hsub hS₂
  obtain ⟨W₃, hm₃, hw₃⟩ := exists_side_walk hnd hEnds hMeets hr hsub hS₃
  obtain ⟨W₄, hm₄, hw₄⟩ := exists_side_walk hnd hEnds hMeets hr hsub hS₄
  
  have hv₁ : K.walkVertices (sqNE c r) W₁ ⊆ segment ℝ (sqNE c r) (sqNW c r) :=
    walkVertices_squareGraph_subset (left_mem_segment ℝ _ _) fun Q hQ => ((hm₁ Q).1 hQ).2
  have hv₂ : K.walkVertices (sqNW c r) W₂ ⊆ segment ℝ (sqNW c r) (sqSW c r) :=
    walkVertices_squareGraph_subset (left_mem_segment ℝ _ _) fun Q hQ => ((hm₂ Q).1 hQ).2
  have hv₃ : K.walkVertices (sqSW c r) W₃ ⊆ segment ℝ (sqSW c r) (sqSE c r) :=
    walkVertices_squareGraph_subset (left_mem_segment ℝ _ _) fun Q hQ => ((hm₃ Q).1 hQ).2
  
  have hc₁ : K.IsIncWalk (sqCoord c r) (sqNE c r) W₁ (sqNW c r) :=
    hw₁.congr_walkVertices fun x hx => (sqCoord_top (hv₁ hx)).symm
  have hc₂ : K.IsIncWalk (sqCoord c r) (sqNW c r) W₂ (sqSW c r) :=
    (hw₂.const_add (2 * r)).congr_walkVertices fun x hx => (sqCoord_left hr.le (hv₂ hx)).symm
  have hc₃ : K.IsIncWalk (sqCoord c r) (sqSW c r) W₃ (sqSE c r) :=
    (hw₃.const_add (4 * r)).congr_walkVertices fun x hx => (sqCoord_bottom hr (hv₃ hx)).symm
  
  obtain ⟨W₄', e, z, hW₄eq, hw₄', hlinke, hlte⟩ :=
    (hw₄.const_add (6 * r)).split_last (sqSE_ne_sqNE c hr)
  have hv₄ : K.walkVertices (sqSE c r) W₄' ⊆ segment ℝ (sqSE c r) (sqNE c r) :=
    walkVertices_squareGraph_subset (left_mem_segment ℝ _ _) fun Q hQ =>
      ((hm₄ Q).1 (by rw [hW₄eq]; exact List.mem_append_left _ hQ)).2
  have hzright : z ∈ segment ℝ (sqSE c r) (sqNE c r) :=
    hv₄ hw₄'.isWalk.target_mem_walkVertices
  have hne₄ : ∀ x ∈ K.walkVertices (sqSE c r) W₄', x ≠ sqNE c r := by
    intro x hx hxeq
    have h1 := hw₄'.le_target x hx
    rw [hxeq] at h1
    exact absurd hlte (not_lt.2 h1)
  have hzne : z ≠ sqNE c r := hne₄ z hw₄'.isWalk.target_mem_walkVertices
  have hc₄ : K.IsIncWalk (sqCoord c r) (sqSE c r) W₄' z :=
    hw₄'.congr_walkVertices fun x hx => (sqCoord_right hr (hv₄ hx) (hne₄ x hx)).symm
  set D : List Piece := W₁ ++ W₂ ++ W₃ ++ W₄' with hDdef
  have hD : K.IsIncWalk (sqCoord c r) (sqNE c r) D z := ((hc₁.append hc₂).append hc₃).append hc₄
  have hin₁ : ∀ Q ∈ W₁, Q ∈ D := fun Q h => by
    rw [hDdef]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
  have hin₂ : ∀ Q ∈ W₂, Q ∈ D := fun Q h => by
    rw [hDdef]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  have hin₃ : ∀ Q ∈ W₃, Q ∈ D := fun Q h => by
    rw [hDdef]; exact List.mem_append_left _ (List.mem_append_right _ h)
  have hin₄ : ∀ Q ∈ W₄', Q ∈ D := fun Q h => by
    rw [hDdef]; exact List.mem_append_right _ h
  
  have heE₄ : e ∈ sideEdges pieces points c r (sqSE c r, sqNE c r) :=
    (hm₄ e).1 (by rw [hW₄eq]; simp)
  have hendeg : e.Nondeg := overlayPieces_nondeg points hnd e heE₄.1.1
  have henotD : e ∉ D := by
    rw [hDdef]
    simp only [List.mem_append, not_or]
    refine ⟨⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩, fun h => ?_⟩
    · exact not_nondeg_of_seg_subset_singleton (t := sqNE c r) (fun y hy =>
        eq_sqNE_of_mem_top_right hr.le (((hm₁ e).1 h).2 hy) (heE₄.2 hy)) hendeg
    · exact notMem_left_of_mem_right hr (heE₄.2 (left_mem_segment ℝ e.1 e.2))
        (((hm₂ e).1 h).2 (left_mem_segment ℝ e.1 e.2))
    · exact not_nondeg_of_seg_subset_singleton (t := sqSE c r) (fun y hy =>
        eq_sqSE_of_mem_bottom_right hr.le (((hm₃ e).1 h).2 hy) (heE₄.2 hy)) hendeg
    · have hnodup : W₄.Nodup := hw₄.isPath.nodup
      rw [hW₄eq] at hnodup
      exact (List.nodup_append.1 hnodup).2.2 e h e (by simp) rfl
  have hcyc : K.IsCycleThrough e (sqNE c r) z D := ⟨hlinke.symm, hD.isPath, henotD⟩
  
  have hNWmem : sqNW c r ∈ K.walkVertices (sqNE c r) D :=
    Graph.walkVertices_mono hin₁ hc₁.isWalk.target_mem_walkVertices
  have hNWnez : sqNW c r ≠ z := by
    intro h
    have h1 : sqCoord c r (sqNW c r) = 2 * r := by
      rw [sqCoord_top (right_mem_segment ℝ _ _), dist_sqNE_sqNW c hr.le]
    have h2 : sqCoord c r z = 6 * r + dist (sqSE c r) z := sqCoord_right hr hzright hzne
    rw [h, h2] at h1
    have := dist_nonneg (x := sqSE c r) (y := z)
    linarith
  refine ⟨e, sqNE c r, z, D, sqNW c r, ⟨hcyc, hNWmem, sqNW_ne_sqNE c hr, hNWnez⟩, ?_⟩
  
  have hEsub : ∀ Q ∈ squareEdges pieces points c r, Q ∈ D ++ [e] := by
    intro Q hQ
    obtain ⟨S, hS, hQS⟩ := exists_side_of_mem_squareEdges hr hQ
    simp only [squarePieces, List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl | rfl
    · exact List.mem_append_left _ (hin₁ Q ((hm₁ Q).2 hQS))
    · exact List.mem_append_left _ (hin₂ Q ((hm₂ Q).2 hQS))
    · exact List.mem_append_left _ (hin₃ Q ((hm₃ Q).2 hQS))
    · have hQ₄ : Q ∈ W₄ := (hm₄ Q).2 hQS
      rw [hW₄eq] at hQ₄
      rcases List.mem_append.1 hQ₄ with h | h
      · exact List.mem_append_left _ (hin₄ Q h)
      · exact List.mem_append_right _ h
  
  have hVsub : V(K) ⊆ K.walkVertices (sqNE c r) D := by
    rintro y ⟨Q, hQ, hy⟩
    rcases List.mem_append.1 (hEsub Q hQ) with h | h
    · exact Graph.mem_walkVertices_of_mem_covered ⟨Q, h, inc_of_mem_squareEdges hQ hy⟩
    · rw [List.mem_singleton] at h
      subst h
      have hyz : y = z ∨ y = sqNE c r := by
        rcases hlinke.2 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hy with rfl | rfl
        exacts [Or.inl h₁.symm, Or.inr h₂.symm, Or.inr h₂.symm, Or.inl h₁.symm]
      rcases hyz with rfl | rfl
      exacts [hD.isWalk.target_mem_walkVertices, Graph.mem_walkVertices_self]
  refine le_antisymm hcyc.cycleGraph_le ⟨?_, ?_⟩
  · rw [hcyc.cycleGraph_vertexSet]
    exact hVsub
  · intro Q x y hlink
    simp only [Graph.cycleGraph, Graph.pathGraphOf_isLink]
    refine ⟨hEsub Q hlink.1, hlink, ?_, ?_⟩ <;> rw [hcyc.walkVertices_round]
    exacts [hVsub hlink.left_mem, hVsub hlink.right_mem]

 


theorem squareGraph_isTwoConnected (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points) (hr : 0 < r)
    (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) :
    (squareGraph pieces points c r).IsTwoConnected := by
  obtain ⟨e, u, v, D, w, hlong, heq⟩ :=
    exists_isLongCycle_squareGraph hnd hEnds hMeets hr hsub
  exact heq ▸ hlong.isTwoConnected

 


theorem squaresTwoConnected : SquaresTwoConnected :=
  fun _ _ hnd hEnds hMeets _ _ hr hsub =>
    squareGraph_isTwoConnected hnd hEnds hMeets hr hsub

end Schoenflies
