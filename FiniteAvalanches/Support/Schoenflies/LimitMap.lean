/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/LimitMap.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.RefinementStars
import FiniteAvalanches.Support.Schoenflies.Inversion

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




















































































open Set Metric Bornology Filter
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

 







 
theorem outerCells_subset_cells : S.outerCells ⊆ S.cells := by
  rintro κ (hv | he)
  · exact S.mem_cells_of_mem_vertexSet (S.outerGraph_le.vertexSet_mono hv)
  · exact S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono he)

 

theorem mem_faces_of_notMem_skel {σ : γ} (hσ : σ ∈ S.cells) (h : σ ∉ V(S.skel) ∪ E(S.skel)) :
    σ ∈ S.faces := by
  rcases hσ with hσ | hσ
  · exact absurd hσ h
  · exact hσ

 

theorem mem_skel_of_sub_face (hS : S.CombInvariants) {σ F : γ}
    (hσ : σ ∈ S.cells) (hsub : S.sub σ F) (hne : σ ≠ F) : σ ∈ V(S.skel) ∪ E(S.skel) := by
  rcases hσ with hσ | hσ
  · exact hσ
  · exact absurd (hS.face_maximal hσ hsub).symm hne

 
theorem notMem_outerCells_of_mem_faces {F : γ} (hF : F ∈ S.faces) : F ∉ S.outerCells := by
  rintro (hv | he)
  · exact S.faces_ne_vertexSet hF (S.outerGraph_le.vertexSet_mono hv) rfl
  · exact S.faces_ne_edgeSet hF (S.outerGraph_le.edgeSet_mono he) rfl

 

theorem notMem_outerCells_of_nonboundary_edge {f : γ} (hf : f ∈ E(S.skel))
    (h : f ∉ E(S.outerGraph)) : f ∉ S.outerCells := by
  rintro (hv | he)
  · exact S.vertexSet_ne_edgeSet (S.outerGraph_le.vertexSet_mono hv) hf rfl
  · exact h he

namespace Realization

variable (R : S.Realization)

 


theorem pointSet_map_eq_iUnion_cell {H : Graph γ γ} (hH : H ≤ S.skel) :
    Graph.pointSet (H.map R.pos) R.drawing = ⋃ κ ∈ V(H) ∪ E(H), R.cell κ := by
  refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion₂_subset fun κ hκ => ?_)
  · rcases hz with hz | hz
    · 
      rw [Graph.vertexSet_map] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      exact Set.mem_biUnion (Or.inl hv)
        (by rw [R.cell_vertex (hH.vertexSet_mono hv)]; rfl)
    · 
      rw [Graph.edgeSet_map] at hz
      obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hz
      obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
      by_cases hend : z ∈ ({R.pos a, R.pos b} : Set Plane)
      · rcases hend with rfl | rfl
        · exact Set.mem_biUnion (Or.inl hl.left_mem)
            (by rw [R.cell_vertex (hH.vertexSet_mono hl.left_mem)]; rfl)
        · exact Set.mem_biUnion (Or.inl hl.right_mem)
            (by rw [R.cell_vertex (hH.vertexSet_mono hl.right_mem)]; rfl)
      · exact Set.mem_biUnion (Or.inr he) (by rw [R.cell_edge (hl.mono hH)]; exact ⟨hze, hend⟩)
  · rcases hκ with hv | he
    · rw [R.cell_vertex (hH.vertexSet_mono hv)]
      exact Set.singleton_subset_iff.2 (Graph.vertexSet_subset_pointSet
        (by rw [Graph.vertexSet_map]; exact ⟨κ, hv, rfl⟩))
    · obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
      rw [R.cell_edge (hl.mono hH)]
      exact Set.Subset.trans Set.sdiff_subset
        (Graph.edgeArc_subset_pointSet (by rw [Graph.edgeSet_map]; exact he))

 
theorem skeletonSet_eq_iUnion_cell :
    R.skeletonSet = ⋃ κ ∈ V(S.skel) ∪ E(S.skel), R.cell κ :=
  R.pointSet_map_eq_iUnion_cell le_rfl

 


theorem outerSet_eq_iUnion_cell : R.outerSet = ⋃ κ ∈ S.outerCells, R.cell κ :=
  R.pointSet_map_eq_iUnion_cell S.outerGraph_le

variable {R}

theorem cell_subset_outerSet {κ : γ} (hκ : κ ∈ S.outerCells) : R.cell κ ⊆ R.outerSet := by
  rw [R.outerSet_eq_iUnion_cell]; exact Set.subset_biUnion_of_mem hκ

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ : γ} {x : Plane}

 


theorem cell_disjoint_outerSet (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells)
    (hout : σ ∉ S.outerCells) : Disjoint (R.cell σ) R.outerSet := by
  rw [R.outerSet_eq_iUnion_cell, Set.disjoint_iUnion₂_right]
  intro κ hκ
  exact h.disjoint hσ (outerCells_subset_cells hκ) (fun hcon => hout (hcon ▸ hκ))

 


theorem cell_disjoint_biUnion (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) {K : Set γ}
    (hK : K ⊆ S.cells) (hnot : σ ∉ K) : Disjoint (R.cell σ) (⋃ κ ∈ K, R.cell κ) := by
  rw [Set.disjoint_iUnion₂_right]
  exact fun κ hκ => h.disjoint hσ (hK hκ) fun hcon => hnot (hcon ▸ hκ)

 
theorem cell_disjoint_skeletonSet (h : R.IsCellDecomposition D) {F : γ} (hF : F ∈ S.faces) :
    Disjoint (R.cell F) R.skeletonSet := by
  rw [R.skeletonSet_eq_iUnion_cell]
  refine h.cell_disjoint_biUnion (S.mem_cells_of_mem_faces hF) (fun κ hκ => ?_) ?_
  · rcases hκ with hv | he
    exacts [S.mem_cells_of_mem_vertexSet hv, S.mem_cells_of_mem_edgeSet he]
  · rintro (hv | he)
    exacts [S.faces_ne_vertexSet hF hv rfl, S.faces_ne_edgeSet hF he rfl]

 
theorem skeletonSet_subset_domain (h : R.IsCellDecomposition D) : R.skeletonSet ⊆ D := by
  rw [R.skeletonSet_eq_iUnion_cell]
  refine Set.iUnion₂_subset fun κ hκ => h.cell_subset_domain ?_
  rcases hκ with hv | he
  exacts [S.mem_cells_of_mem_vertexSet hv, S.mem_cells_of_mem_edgeSet he]

 




theorem star_face_eq_closure (h : R.IsCellDecomposition D) (hS : S.CombInvariants) {F : γ}
    (hF : F ∈ S.faces) : R.star F = closure (R.cell F) := by
  rw [h.star_eq_faces hS (S.mem_cells_of_mem_faces hF)]
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun T hT => ?_)
    (Set.subset_biUnion_of_mem (u := fun T => closure (R.cell T))
      (show F ∈ {T | T ∈ S.faces ∧ S.sub F T} from
        ⟨hF, h.sub_refl (S.mem_cells_of_mem_faces hF)⟩))
  exact (congrArg (fun c => closure (R.cell c)) (hS.face_maximal hF hT.2)).le

 
theorem carrier_mem_outerCells [Nonempty γ] (h : R.IsCellDecomposition D)
    (hx : x ∈ R.outerSet) : R.carrier x ∈ S.outerCells := by
  rw [R.outerSet_eq_iUnion_cell] at hx
  obtain ⟨κ, hκ, hxκ⟩ := Set.mem_iUnion₂.1 hx
  rwa [h.carrier_eq (outerCells_subset_cells hκ) hxκ]

 



theorem closure_cell_meets_outer_iff (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    (closure (R.cell τ) ∩ R.outerSet).Nonempty ↔ ∃ κ ∈ S.outerCells, S.sub κ τ := by
  constructor
  · rintro ⟨p, hpτ, hpout⟩
    rw [R.outerSet_eq_iUnion_cell] at hpout
    obtain ⟨κ, hκ, hpκ⟩ := Set.mem_iUnion₂.1 hpout
    exact ⟨κ, hκ, h.sub_of_mem (outerCells_subset_cells hκ) hτ hpκ hpτ⟩
  · rintro ⟨κ, hκ, hsub⟩
    obtain ⟨z, hz⟩ := h.nonempty (outerCells_subset_cells hκ)
    exact ⟨z, h.subset_closure (outerCells_subset_cells hκ) hτ hsub hz, cell_subset_outerSet hκ hz⟩

 

theorem star_meets_outer_iff (h : R.IsCellDecomposition D)
    (hS : S.CombInvariants) (σ : γ) :
    (R.star σ ∩ R.outerSet).Nonempty ↔ ∃ τ, S.sub σ τ ∧ ∃ κ ∈ S.outerCells, S.sub κ τ := by
  constructor
  · rintro ⟨p, hpstar, hpout⟩
    obtain ⟨τ, hτ, hpτ⟩ := mem_star_iff.1 hpstar
    exact ⟨τ, hτ, (h.closure_cell_meets_outer_iff (hS.sub_mem_right hτ)).1 ⟨p, hpτ, hpout⟩⟩
  · rintro ⟨τ, hτ, hex⟩
    obtain ⟨p, hpτ, hpout⟩ := (h.closure_cell_meets_outer_iff (hS.sub_mem_right hτ)).2 hex
    exact ⟨p, closure_cell_subset_star hτ hpτ, hpout⟩

end IsCellDecomposition

end Realization

 




 














structure LimitTower (γ : Type*) [Nonempty γ] where
   
  str : ℕ → CellStructure γ
   
  src : ∀ n, (str n).Realization
   
  tgt : ∀ n, (str n).Realization
   
  skelHomeo : ∀ n, SkeletonHomeo (src n) (tgt n)
   
  par : ℕ → γ → γ
   
  dom : Set Plane
   
  bdry : Set Plane
   
  dom' : Set Plane
   
  bdry' : Set Plane
   
  eps : ℕ → ℝ
   
  srcDecomp : ∀ n, (src n).IsCellDecomposition dom
   
  tgtDecomp : ∀ n, (tgt n).IsCellDecomposition dom'
   
  comb : ∀ n, (str n).CombInvariants
   
  srcRefines : ∀ n, (src (n + 1)).Refines (src n) (par n)
   
  tgtRefines : ∀ n, (tgt (n + 1)).Refines (tgt n) (par n)
   
  srcOuterSet : ∀ n, (src n).outerSet = bdry
   
  tgtOuterSet : ∀ n, (tgt n).outerSet = bdry'
   
  isClosed_dom : IsClosed dom
   
  isClosed_dom' : IsClosed dom'
   

  isBounded_dom : IsBounded dom
   
  isBounded_dom' : IsBounded dom'
   
  isOpen_int : IsOpen (dom \ bdry)
   
  isOpen_int' : IsOpen (dom' \ bdry')
   
  skeletonSet_mono : ∀ n, (src n).skeletonSet ⊆ (src (n + 1)).skeletonSet
   

  skelHomeo_succ : ∀ n,
    Set.EqOn (skelHomeo (n + 1)).toFun (skelHomeo n).toFun (src n).skeletonSet
   

  diam_tgtStar_le : ∀ n, ∀ ⦃σ⦄, σ ∈ (str n).cells → diam ((tgt n).star σ) ≤ eps n
   
  tendsto_eps : Tendsto eps atTop (nhds 0)
   

  tendsto_diam_srcStar : ∀ ⦃x⦄, x ∈ dom \ bdry →
    Tendsto (fun n => diam ((src n).star ((src n).carrier x))) atTop (nhds 0)

namespace LimitTower

variable [Nonempty γ] (L : LimitTower γ) {x y z : Plane} {m n : ℕ} {σ : γ}

 
def region : Set Plane := L.dom \ L.bdry

 
def region' : Set Plane := L.dom' \ L.bdry'

 

def tgtStar (n : ℕ) (x : Plane) : Set Plane := (L.tgt n).star ((L.src n).carrier x)

 
def srcStar (n : ℕ) (x : Plane) : Set Plane := (L.src n).star ((L.src n).carrier x)

variable {L}

theorem mem_region_iff : x ∈ L.region ↔ x ∈ L.dom ∧ x ∉ L.bdry := Iff.rfl

theorem mem_region'_iff : x ∈ L.region' ↔ x ∈ L.dom' ∧ x ∉ L.bdry' := Iff.rfl

theorem region_subset_dom : L.region ⊆ L.dom := Set.sdiff_subset

theorem region'_subset_dom' : L.region' ⊆ L.dom' := Set.sdiff_subset

theorem isOpen_region (L : LimitTower γ) : IsOpen L.region := L.isOpen_int

theorem isOpen_region' (L : LimitTower γ) : IsOpen L.region' := L.isOpen_int'

theorem tgtStar_eq (n : ℕ) (x : Plane) :
    L.tgtStar n x = (L.tgt n).star ((L.src n).carrier x) := rfl

theorem srcStar_eq (n : ℕ) (x : Plane) :
    L.srcStar n x = (L.src n).star ((L.src n).carrier x) := rfl

 

theorem exists_lt_of_tendsto_zero {f : ℕ → ℝ} (h : Tendsto f atTop (nhds 0)) {r : ℝ}
    (hr : 0 < r) : ∃ n, f n < r :=
  (h.eventually (Iio_mem_nhds hr)).exists

 

theorem srcStar_subset_dom (n : ℕ) (σ : γ) : (L.src n).star σ ⊆ L.dom :=
  ((L.srcDecomp n).star_subset_closure_domain (L.comb n)).trans L.isClosed_dom.closure_subset

theorem tgtStar_subset_dom' (n : ℕ) (σ : γ) : (L.tgt n).star σ ⊆ L.dom' :=
  ((L.tgtDecomp n).star_subset_closure_domain (L.comb n)).trans L.isClosed_dom'.closure_subset

theorem isBounded_tgt_star (n : ℕ) (σ : γ) : IsBounded ((L.tgt n).star σ) :=
  (L.tgtDecomp n).isBounded_star (L.comb n) L.isBounded_dom'

theorem isBounded_src_star (n : ℕ) (σ : γ) : IsBounded ((L.src n).star σ) :=
  (L.srcDecomp n).isBounded_star (L.comb n) L.isBounded_dom

theorem isBounded_srcStar (n : ℕ) (x : Plane) : IsBounded (L.srcStar n x) :=
  isBounded_src_star n _

theorem isBounded_tgtStar (n : ℕ) (x : Plane) : IsBounded (L.tgtStar n x) :=
  isBounded_tgt_star n _

theorem mem_srcStar_self (hx : x ∈ L.dom) (n : ℕ) : x ∈ L.srcStar n x :=
  (L.srcDecomp n).mem_star_carrier hx

theorem tendsto_diam_srcStar_point (hx : x ∈ L.region) :
    Tendsto (fun n => diam (L.srcStar n x)) atTop (nhds 0) :=
  L.tendsto_diam_srcStar hx

 
theorem tgtStar_succ_subset (hx : x ∈ L.dom) (n : ℕ) : L.tgtStar (n + 1) x ⊆ L.tgtStar n x :=
  (L.srcRefines n).target_star_subset (L.tgtRefines n) (L.comb (n + 1)) (L.srcDecomp n)
    (L.srcDecomp (n + 1)) hx

theorem tgtStar_antitone (hx : x ∈ L.dom) : Antitone (fun n => L.tgtStar n x) :=
  antitone_nat_of_succ_le (L.tgtStar_succ_subset hx)

theorem tgtStar_nonempty (hx : x ∈ L.dom) (n : ℕ) : (L.tgtStar n x).Nonempty :=
  (L.tgtDecomp n).star_nonempty ((L.srcDecomp n).mem_cells_carrier hx)

theorem isCompact_tgtStar (n : ℕ) (x : Plane) : IsCompact (L.tgtStar n x) :=
  (L.tgtDecomp n).isCompact_star (L.comb n) L.isBounded_dom'

theorem diam_tgtStar (hx : x ∈ L.dom) (n : ℕ) : diam (L.tgtStar n x) ≤ L.eps n :=
  L.diam_tgtStar_le n ((L.srcDecomp n).mem_cells_carrier hx)

theorem tendsto_diam_tgtStar (hx : x ∈ L.dom) :
    Tendsto (fun n => diam (L.tgtStar n x)) atTop (nhds 0) :=
  squeeze_zero (fun _ => diam_nonneg) (L.diam_tgtStar hx) L.tendsto_eps

 

theorem exists_eq_singleton_iInter_tgtStar (hx : x ∈ L.dom) :
    ∃ p, ⋂ n, L.tgtStar n x = {p} :=
  Plane.eq_singleton_iInter_of_diam_tendsto_zero (L.tgtStar_nonempty hx)
    (fun n => L.isCompact_tgtStar n x) (L.tgtStar_antitone hx) (L.tendsto_diam_tgtStar hx)

open scoped Classical in
 

noncomputable def F (L : LimitTower γ) (x : Plane) : Plane :=
  if h : ∃ p, ⋂ n, L.tgtStar n x = {p} then h.choose else 0

 
theorem iInter_tgtStar_eq (hx : x ∈ L.dom) : ⋂ n, L.tgtStar n x = {L.F x} := by
  rw [F, dif_pos (L.exists_eq_singleton_iInter_tgtStar hx)]
  exact (L.exists_eq_singleton_iInter_tgtStar hx).choose_spec

theorem F_mem_iInter (hx : x ∈ L.dom) : L.F x ∈ ⋂ n, L.tgtStar n x := by
  rw [L.iInter_tgtStar_eq hx]
  exact rfl

theorem F_mem_tgtStar (hx : x ∈ L.dom) (n : ℕ) : L.F x ∈ L.tgtStar n x :=
  Set.mem_iInter.1 (L.F_mem_iInter hx) n

 
theorem eq_F_of_mem_iInter (hx : x ∈ L.dom) (hz : ∀ n, z ∈ L.tgtStar n x) : z = L.F x := by
  have : z ∈ ⋂ n, L.tgtStar n x := Set.mem_iInter.2 hz
  rwa [L.iInter_tgtStar_eq hx, Set.mem_singleton_iff] at this

theorem F_mem_dom' (hx : x ∈ L.dom) : L.F x ∈ L.dom' :=
  tgtStar_subset_dom' 0 _ (L.F_mem_tgtStar hx 0)

 
theorem dist_F_le_of_mem_tgtStar (hx : x ∈ L.dom) (hz : z ∈ L.tgtStar n x) :
    dist (L.F x) z ≤ L.eps n :=
  le_trans (dist_le_diam_of_mem (isBounded_tgt_star n _) (L.F_mem_tgtStar hx n) hz)
    (L.diam_tgtStar hx n)

 





theorem skeletonSet_mono_le (hmn : m ≤ n) : (L.src m).skeletonSet ⊆ (L.src n).skeletonSet := by
  induction n, hmn using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact ih.trans (L.skeletonSet_mono n)

 
theorem skelHomeo_eqOn (hmn : m ≤ n) :
    Set.EqOn (L.skelHomeo n).toFun (L.skelHomeo m).toFun (L.src m).skeletonSet := by
  induction n, hmn using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ n hmn ih =>
    intro w hw
    rw [L.skelHomeo_succ n (skeletonSet_mono_le hmn hw), ih hw]

 


theorem skelHomeo_mem_tgtStar (hx : x ∈ (L.src n).skeletonSet) :
    (L.skelHomeo n).toFun x ∈ L.tgtStar n x := by
  rw [(L.src n).skeletonSet_eq_iUnion_cell] at hx
  obtain ⟨κ, hκ, hxκ⟩ := Set.mem_iUnion₂.1 hx
  have hcells : κ ∈ (L.str n).cells := by
    rcases hκ with hv | he
    exacts [(L.str n).mem_cells_of_mem_vertexSet hv, (L.str n).mem_cells_of_mem_edgeSet he]
  have hgx : (L.skelHomeo n).toFun x ∈ (L.tgt n).cell κ := by
    rw [← (L.skelHomeo n).image_cell hκ]
    exact Set.mem_image_of_mem _ hxκ
  rw [tgtStar_eq, (L.srcDecomp n).carrier_eq hcells hxκ]
  exact Realization.closure_cell_subset_star ((L.tgtDecomp n).sub_refl hcells)
    (_root_.subset_closure hgx)

 

theorem F_eq_skelHomeo (hx : x ∈ (L.src n).skeletonSet) (hxD : x ∈ L.dom) :
    L.F x = (L.skelHomeo n).toFun x := by
  refine (eq_F_of_mem_iInter hxD fun m => ?_).symm
  rcases le_or_gt n m with hnm | hmn
  · rw [← skelHomeo_eqOn hnm hx]
    exact skelHomeo_mem_tgtStar (skeletonSet_mono_le hnm hx)
  · exact tgtStar_antitone hxD hmn.le (skelHomeo_mem_tgtStar hx)

 

 



theorem tgtStar_subset_of_mem_cellNbhd (hx : x ∈ L.dom) (hzD : z ∈ L.dom)
    (hz : z ∈ (L.src n).cellNbhd x) : L.tgtStar n z ⊆ L.tgtStar n x :=
  (L.tgtDecomp n).star_anti_of_sub (L.comb n) ((L.srcDecomp n).mem_cells_carrier hx)
    ((L.srcDecomp n).mem_cells_carrier hzD)
    ((L.srcDecomp n).sub_carrier_of_mem_cellNbhd hx hz hzD)

 

theorem continuousOn_F (L : LimitTower γ) : ContinuousOn L.F L.dom := by
  rw [Metric.continuousOn_iff]
  intro x hx η hη
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero L.tendsto_eps hη
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.1 ((L.src n).isOpen_cellNbhd x) x ((L.src n).mem_cellNbhd_self x)
  refine ⟨δ, hδ, fun a ha hadist => ?_⟩
  rw [dist_comm]
  exact lt_of_le_of_lt (dist_F_le_of_mem_tgtStar hx
    (tgtStar_subset_of_mem_cellNbhd hx ha (hball (Metric.mem_ball.2 hadist))
      (L.F_mem_tgtStar ha n))) hn

 

 


theorem star_meets_bdry_iff (L : LimitTower γ) (n : ℕ) (σ : γ) :
    ((L.src n).star σ ∩ L.bdry).Nonempty ↔ ((L.tgt n).star σ ∩ L.bdry').Nonempty := by
  rw [← L.srcOuterSet n, ← L.tgtOuterSet n, (L.srcDecomp n).star_meets_outer_iff (L.comb n) σ,
    (L.tgtDecomp n).star_meets_outer_iff (L.comb n) σ]

 

theorem exists_srcStar_subset_region (hx : x ∈ L.region) : ∃ n, L.srcStar n x ⊆ L.region := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 L.isOpen_region x hx
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero (L.tendsto_diam_srcStar hx) hr
  refine ⟨n, fun w hw => hball (Metric.mem_ball.2 (lt_of_le_of_lt ?_ hn))⟩
  exact dist_le_diam_of_mem (isBounded_srcStar n x) hw
    (mem_srcStar_self (region_subset_dom hx) n)

 
theorem F_mem_region' (hx : x ∈ L.region) : L.F x ∈ L.region' := by
  obtain ⟨n, hn⟩ := exists_srcStar_subset_region hx
  refine ⟨F_mem_dom' (region_subset_dom hx), fun hcon => ?_⟩
  obtain ⟨w, hw, hwb⟩ := (L.star_meets_bdry_iff n ((L.src n).carrier x)).2
    ⟨L.F x, L.F_mem_tgtStar (region_subset_dom hx) n, hcon⟩
  exact (hn hw).2 hwb

 

 

theorem injOn_F (L : LimitTower γ) : Set.InjOn L.F L.region := by
  intro x hx y hy hxy
  
  have hmeet : ∀ n, (L.srcStar n x ∩ L.srcStar n y).Nonempty := fun n =>
    (Realization.star_inter_nonempty_congr (L.tgtDecomp n) (L.srcDecomp n) (L.comb n)).1
      ⟨L.F x, L.F_mem_tgtStar (region_subset_dom hx) n,
        hxy ▸ L.F_mem_tgtStar (region_subset_dom hy) n⟩
  have hbound : ∀ n, dist x y ≤ diam (L.srcStar n x) + diam (L.srcStar n y) := by
    intro n
    obtain ⟨w, hwx, hwy⟩ := hmeet n
    refine le_trans (dist_triangle x w y) (add_le_add ?_ ?_)
    · exact dist_le_diam_of_mem (isBounded_srcStar n x)
        (mem_srcStar_self (region_subset_dom hx) n) hwx
    · exact dist_le_diam_of_mem (isBounded_srcStar n y) hwy
        (mem_srcStar_self (region_subset_dom hy) n)
  have hzero : dist x y ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds
      (by simpa using (tendsto_diam_srcStar_point hx).add (tendsto_diam_srcStar_point hy)) hbound
  exact dist_le_zero.1 hzero

 

 

theorem tgt_cell_subset_region' (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).cells)
    (hout : σ ∉ (L.str n).outerCells) : (L.tgt n).cell σ ⊆ L.region' := by
  intro w hw
  refine ⟨(L.tgtDecomp n).cell_subset_domain hσ hw, fun hb => ?_⟩
  rw [← L.tgtOuterSet n] at hb
  exact Set.disjoint_left.1 ((L.tgtDecomp n).cell_disjoint_outerSet hσ hout) hw hb

 



theorem exists_mem_tgt_skeletonSet (hy : y ∈ L.region') {δ : ℝ} (hδ : 0 < δ) :
    ∃ n w, w ∈ (L.tgt n).skeletonSet ∧ w ∈ L.region' ∧ dist y w < δ := by
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero L.tendsto_eps hδ
  by_cases hys : y ∈ (L.tgt n).skeletonSet
  · exact ⟨n, y, hys, hy, by simpa using hδ⟩
  have hyD : y ∈ L.dom' := region'_subset_dom' hy
  have hcar : (L.tgt n).carrier y ∈ (L.str n).cells := (L.tgtDecomp n).mem_cells_carrier hyD
  
  have hface : (L.tgt n).carrier y ∈ (L.str n).faces := by
    refine mem_faces_of_notMem_skel hcar fun hmem => hys ?_
    exact Realization.cell_subset_skeletonSet hmem ((L.tgtDecomp n).mem_cell_carrier hyD)
  obtain ⟨f, hf, hfout, hfsub⟩ := (L.comb n).nonboundary_edge hface
  have hfc : f ∈ (L.str n).cells := (L.str n).mem_cells_of_mem_edgeSet hf
  obtain ⟨w, hw⟩ := (L.tgtDecomp n).nonempty hfc
  have hwstar : w ∈ (L.tgt n).star ((L.tgt n).carrier y) :=
    Realization.closure_cell_subset_star ((L.tgtDecomp n).sub_refl hcar)
      ((L.tgtDecomp n).subset_closure hfc hcar hfsub hw)
  refine ⟨n, w, Realization.cell_subset_skeletonSet (Or.inr hf) hw,
    tgt_cell_subset_region' n hfc (notMem_outerCells_of_nonboundary_edge hf hfout) hw,
    lt_of_le_of_lt (le_trans (dist_le_diam_of_mem (isBounded_tgt_star n _)
      ((L.tgtDecomp n).mem_star_carrier hyD) hwstar) (L.diam_tgtStar_le n hcar)) hn⟩

 






 

def preStar (L : LimitTower γ) (n : ℕ) (y : Plane) : Set Plane :=
  (L.src n).star ((L.tgt n).carrier y)

theorem preStar_succ_subset (hy : y ∈ L.dom') (n : ℕ) :
    L.preStar (n + 1) y ⊆ L.preStar n y :=
  (L.tgtRefines n).target_star_subset (L.srcRefines n) (L.comb (n + 1)) (L.tgtDecomp n)
    (L.tgtDecomp (n + 1)) hy

theorem preStar_nonempty (hy : y ∈ L.dom') (n : ℕ) : (L.preStar n y).Nonempty :=
  (L.srcDecomp n).star_nonempty ((L.tgtDecomp n).mem_cells_carrier hy)

theorem isCompact_preStar (n : ℕ) (y : Plane) : IsCompact (L.preStar n y) :=
  (L.srcDecomp n).isCompact_star (L.comb n) L.isBounded_dom

theorem nonempty_iInter_preStar (hy : y ∈ L.dom') : (⋂ n, L.preStar n y).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (fun n => preStar_succ_subset hy n) (preStar_nonempty hy) (isCompact_preStar 0 y)
    fun n => (isCompact_preStar n y).isClosed

 


theorem F_eq_of_mem_iInter_preStar (hy : y ∈ L.dom') (hxD : x ∈ L.dom)
    (hx : ∀ n, x ∈ L.preStar n y) : L.F x = y := by
  have hbound : ∀ n, dist (L.F x) y ≤ 2 * L.eps n := by
    intro n
    obtain ⟨τ, hτ, hxτ⟩ := Realization.mem_star_iff.1 (hx n)
    have hτc : τ ∈ (L.str n).cells := (L.comb n).sub_mem_right hτ
    
    have hsub : (L.str n).sub ((L.src n).carrier x) τ :=
      (L.srcDecomp n).sub_of_mem ((L.srcDecomp n).mem_cells_carrier hxD) hτc
        ((L.srcDecomp n).mem_cell_carrier hxD) hxτ
    obtain ⟨w, hw⟩ := (L.tgtDecomp n).nonempty hτc
    have hwx : w ∈ L.tgtStar n x :=
      Realization.closure_cell_subset_star hsub (_root_.subset_closure hw)
    have hwy : w ∈ (L.tgt n).star ((L.tgt n).carrier y) :=
      Realization.closure_cell_subset_star hτ (_root_.subset_closure hw)
    have h₁ : dist (L.F x) w ≤ L.eps n := dist_F_le_of_mem_tgtStar hxD hwx
    have h₂ : dist w y ≤ L.eps n :=
      le_trans (dist_le_diam_of_mem (isBounded_tgt_star n _) hwy
        ((L.tgtDecomp n).mem_star_carrier hy))
        (L.diam_tgtStar_le n ((L.tgtDecomp n).mem_cells_carrier hy))
    calc dist (L.F x) y ≤ dist (L.F x) w + dist w y := dist_triangle _ _ _
      _ ≤ 2 * L.eps n := by linarith
  have hzero : dist (L.F x) y ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds
      (by simpa using L.tendsto_eps.const_mul 2) hbound
  exact dist_le_zero.1 hzero

 

theorem exists_tgt_star_subset_region' (hy : y ∈ L.region') :
    ∃ n, (L.tgt n).star ((L.tgt n).carrier y) ⊆ L.region' := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 L.isOpen_region' y hy
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero L.tendsto_eps hr
  refine ⟨n, fun w hw => hball (Metric.mem_ball.2 ?_)⟩
  have h₁ : dist w y ≤ diam ((L.tgt n).star ((L.tgt n).carrier y)) :=
    dist_le_diam_of_mem (isBounded_tgt_star n _) hw
      ((L.tgtDecomp n).mem_star_carrier (region'_subset_dom' hy))
  have h₂ := L.diam_tgtStar_le n ((L.tgtDecomp n).mem_cells_carrier (region'_subset_dom' hy))
  linarith

 
theorem exists_mem_region_F_eq (hy : y ∈ L.region') : ∃ x, x ∈ L.region ∧ L.F x = y := by
  obtain ⟨n, hn⟩ := exists_tgt_star_subset_region' hy
  obtain ⟨x, hx⟩ := nonempty_iInter_preStar (region'_subset_dom' hy)
  have hmem : ∀ m, x ∈ L.preStar m y := Set.mem_iInter.1 hx
  have hxD : x ∈ L.dom := srcStar_subset_dom 0 _ (hmem 0)
  refine ⟨x, ⟨hxD, fun hb => ?_⟩, F_eq_of_mem_iInter_preStar (region'_subset_dom' hy) hxD hmem⟩
  
  obtain ⟨w, hw, hwb⟩ := (L.star_meets_bdry_iff n ((L.tgt n).carrier y)).1 ⟨x, hmem n, hb⟩
  exact (hn hw).2 hwb

 

 
theorem src_cell_subset_region (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).cells)
    (hout : σ ∉ (L.str n).outerCells) : (L.src n).cell σ ⊆ L.region := by
  intro w hw
  refine ⟨(L.srcDecomp n).cell_subset_domain hσ hw, fun hb => ?_⟩
  rw [← L.srcOuterSet n] at hb
  exact Set.disjoint_left.1 ((L.srcDecomp n).cell_disjoint_outerSet hσ hout) hw hb

 

theorem src_carrier_notMem_outerCells (hx : x ∈ L.region) (n : ℕ) :
    (L.src n).carrier x ∉ (L.str n).outerCells := fun hc =>
  hx.2 (by
    rw [← L.srcOuterSet n]
    exact Realization.cell_subset_outerSet hc ((L.srcDecomp n).mem_cell_carrier hx.1))

theorem tgt_carrier_notMem_outerCells (hy : y ∈ L.region') (n : ℕ) :
    (L.tgt n).carrier y ∉ (L.str n).outerCells := fun hc =>
  hy.2 (by
    rw [← L.tgtOuterSet n]
    exact Realization.cell_subset_outerSet hc ((L.tgtDecomp n).mem_cell_carrier hy.1))

 






theorem F_mem_cell_of_mem_cell_face (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).faces)
    (hx : x ∈ (L.src n).cell σ) : L.F x ∈ (L.tgt n).cell σ := by
  have hσc : σ ∈ (L.str n).cells := (L.str n).mem_cells_of_mem_faces hσ
  have hxr : x ∈ L.region :=
    src_cell_subset_region n hσc (notMem_outerCells_of_mem_faces hσ) hx
  have hcar : (L.src n).carrier x = σ := (L.srcDecomp n).carrier_eq hσc hx
  
  have hclos : L.F x ∈ closure ((L.tgt n).cell σ) := by
    have := L.F_mem_tgtStar hxr.1 n
    rwa [tgtStar_eq, hcar, (L.tgtDecomp n).star_face_eq_closure (L.comb n) hσ] at this
  rw [(L.tgtDecomp n).closure_eq hσc] at hclos
  obtain ⟨ρ, ⟨hρ, hρsub⟩, hFρ⟩ := Set.mem_iUnion₂.1 hclos
  by_cases hρσ : ρ = σ
  · exact hρσ ▸ hFρ
  
  exfalso
  have hFskel : L.F x ∈ (L.tgt n).skeletonSet :=
    Realization.cell_subset_skeletonSet (mem_skel_of_sub_face (L.comb n) hρ hρsub hρσ) hFρ
  obtain ⟨w, hwskel, hwF⟩ : ∃ w ∈ (L.src n).skeletonSet, (L.skelHomeo n).toFun w = L.F x := by
    rw [← (L.skelHomeo n).image_skeletonSet] at hFskel
    exact hFskel
  have hFr : L.F x ∈ L.region' := F_mem_region' hxr
  have hwr : w ∈ L.region := by
    refine ⟨(L.srcDecomp n).skeletonSet_subset_domain hwskel, fun hb => hFr.2 ?_⟩
    rw [← L.tgtOuterSet n, ← hwF, ← (L.skelHomeo n).image_outerSet]
    exact Set.mem_image_of_mem _ (by rwa [L.srcOuterSet n])
  have hwx : w = x := L.injOn_F hwr hxr (by
    rw [F_eq_skelHomeo hwskel hwr.1, hwF])
  exact Set.disjoint_left.1 ((L.srcDecomp n).cell_disjoint_skeletonSet hσ) hx (hwx ▸ hwskel)

 



theorem image_cell (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).cells)
    (hout : σ ∉ (L.str n).outerCells) : L.F '' ((L.src n).cell σ) = (L.tgt n).cell σ := by
  by_cases hskel : σ ∈ V((L.str n).skel) ∪ E((L.str n).skel)
  · 
    rw [Set.image_congr (fun w hw => F_eq_skelHomeo
      (Realization.cell_subset_skeletonSet hskel hw)
      ((L.srcDecomp n).cell_subset_domain hσ hw))]
    exact (L.skelHomeo n).image_cell hskel
  have hface : σ ∈ (L.str n).faces := mem_faces_of_notMem_skel hσ hskel
  refine Set.Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact F_mem_cell_of_mem_cell_face n hface hw
  
  obtain ⟨w, hwr, rfl⟩ := exists_mem_region_F_eq (tgt_cell_subset_region' n hσ hout hy)
  refine Set.mem_image_of_mem _ ?_
  set ρ := (L.src n).carrier w with hρdef
  have hρc : ρ ∈ (L.str n).cells := (L.srcDecomp n).mem_cells_carrier hwr.1
  have hρface : ρ ∈ (L.str n).faces := by
    refine mem_faces_of_notMem_skel hρc fun hmem => ?_
    
    refine Set.disjoint_left.1 ((L.tgtDecomp n).cell_disjoint_skeletonSet hface) hy ?_
    rw [F_eq_skelHomeo (Realization.cell_subset_skeletonSet hmem
      ((L.srcDecomp n).mem_cell_carrier hwr.1)) hwr.1]
    refine Realization.cell_subset_skeletonSet hmem ?_
    rw [← (L.skelHomeo n).image_cell hmem]
    exact Set.mem_image_of_mem _ ((L.srcDecomp n).mem_cell_carrier hwr.1)
  have hin : L.F w ∈ (L.tgt n).cell ρ :=
    F_mem_cell_of_mem_cell_face n hρface ((L.srcDecomp n).mem_cell_carrier hwr.1)
  have : ρ = σ := by
    by_contra hne
    exact Set.disjoint_left.1 ((L.tgtDecomp n).disjoint hρc hσ hne) hin hy
  rw [← this]
  exact (L.srcDecomp n).mem_cell_carrier hwr.1

 
theorem tgt_carrier_F (hx : x ∈ L.region) (n : ℕ) :
    (L.tgt n).carrier (L.F x) = (L.src n).carrier x := by
  refine (L.tgtDecomp n).carrier_eq ((L.srcDecomp n).mem_cells_carrier hx.1) ?_
  rw [← image_cell n ((L.srcDecomp n).mem_cells_carrier hx.1)
    (src_carrier_notMem_outerCells hx n)]
  exact Set.mem_image_of_mem _ ((L.srcDecomp n).mem_cell_carrier hx.1)

 

open scoped Classical in
 



noncomputable def inv (L : LimitTower γ) (y : Plane) : Plane :=
  if h : ∃ x, x ∈ L.region ∧ L.F x = y then h.choose else 0

theorem inv_spec (h : ∃ x, x ∈ L.region ∧ L.F x = y) :
    L.inv y ∈ L.region ∧ L.F (L.inv y) = y := by
  rw [inv, dif_pos h]
  exact h.choose_spec

theorem inv_mem_region (hy : y ∈ L.region') : L.inv y ∈ L.region :=
  (inv_spec (exists_mem_region_F_eq hy)).1

theorem F_inv (hy : y ∈ L.region') : L.F (L.inv y) = y :=
  (inv_spec (exists_mem_region_F_eq hy)).2

theorem inv_F (hx : x ∈ L.region) : L.inv (L.F x) = x :=
  L.injOn_F (inv_spec ⟨x, hx, rfl⟩).1 hx (inv_spec ⟨x, hx, rfl⟩).2

 
theorem src_carrier_inv (hy : y ∈ L.region') (n : ℕ) :
    (L.src n).carrier (L.inv y) = (L.tgt n).carrier y := by
  have h := tgt_carrier_F (inv_mem_region hy) n
  rw [F_inv hy] at h
  exact h.symm

 


theorem continuousOn_inv (L : LimitTower γ) : ContinuousOn L.inv L.region' := by
  rw [Metric.continuousOn_iff]
  intro y hy η hη
  have hxr : L.inv y ∈ L.region := inv_mem_region hy
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero (tendsto_diam_srcStar_point hxr) hη
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.1 ((L.tgt n).isOpen_cellNbhd y) y ((L.tgt n).mem_cellNbhd_self y)
  refine ⟨δ, hδ, fun z hz hzdist => ?_⟩
  have hsub : (L.str n).sub ((L.tgt n).carrier y) ((L.tgt n).carrier z) :=
    (L.tgtDecomp n).sub_carrier_of_mem_cellNbhd (region'_subset_dom' hy)
      (hball (Metric.mem_ball.2 hzdist)) (region'_subset_dom' hz)
  rw [← src_carrier_inv hy n, ← src_carrier_inv hz n] at hsub
  have hmem : L.inv z ∈ L.srcStar n (L.inv y) :=
    (L.srcDecomp n).star_anti_of_sub (L.comb n) ((L.srcDecomp n).mem_cells_carrier hxr.1)
      ((L.srcDecomp n).mem_cells_carrier (inv_mem_region hz).1) hsub
      ((L.srcDecomp n).mem_star_carrier (inv_mem_region hz).1)
  exact lt_of_le_of_lt
    (dist_le_diam_of_mem (isBounded_srcStar n _) hmem (mem_srcStar_self hxr.1 n)) hn

 


theorem isHomeoOn_F (L : LimitTower γ) : IsHomeoOn L.F L.inv L.region L.region' where
  mapsTo := fun _ hx => F_mem_region' hx
  mapsTo_inv := fun _ hy => inv_mem_region hy
  continuousOn := L.continuousOn_F.mono region_subset_dom
  continuousOn_inv := L.continuousOn_inv
  invOn := ⟨fun _ hx => inv_F hx, fun _ hy => F_inv hy⟩

theorem image_region (L : LimitTower γ) : L.F '' L.region = L.region' :=
  L.isHomeoOn_F.image_eq

 

theorem interior_homeomorphism (L : LimitTower γ) :
    IsHomeoOn L.F L.inv L.region L.region' ∧
      ∀ n, ∀ x ∈ (L.src n).skeletonSet, x ∈ L.dom → L.F x = (L.skelHomeo n).toFun x :=
  ⟨L.isHomeoOn_F, fun _ _ hx hxD => F_eq_skelHomeo hx hxD⟩

end LimitTower

end CellStructure

end Schoenflies
