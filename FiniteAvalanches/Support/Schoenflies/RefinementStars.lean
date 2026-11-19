/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/RefinementStars.lean.
-/
import FiniteAvalanches.Support.Schoenflies.GeneratedStructure

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 









































































open Set Metric Bornology
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

 
theorem finite_cells (S : CellStructure γ) : S.cells.Finite :=
  (S.finite_vertexSet.union S.finite_edgeSet).union S.finite_faces

namespace Realization

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

 




theorem mem_star_iff : y ∈ R.star σ ↔ ∃ τ, S.sub σ τ ∧ y ∈ closure (R.cell τ) := by
  simp only [star, Set.mem_iUnion, mem_supercells, exists_prop]

 
theorem closure_cell_subset_star (h : S.sub σ τ) : closure (R.cell τ) ⊆ R.star σ := fun _ hz =>
  mem_star_iff.2 ⟨τ, h, hz⟩

 
theorem finite_supercells (hS : S.CombInvariants) (σ : γ) : (S.supercells σ).Finite :=
  S.finite_cells.subset fun _ hτ => hS.sub_mem_right hτ

 
theorem isClosed_star (hS : S.CombInvariants) : IsClosed (R.star σ) :=
  (finite_supercells hS σ).isClosed_biUnion fun _ _ => isClosed_closure

 




open scoped Classical in
 



noncomputable def carrier [Nonempty γ] (R : S.Realization) (x : Plane) : γ :=
  if h : ∃ σ, σ ∈ S.cells ∧ x ∈ R.cell σ then h.choose else Classical.arbitrary γ

theorem carrier_spec [Nonempty γ] (R : S.Realization) (x : Plane)
    (h : ∃ σ, σ ∈ S.cells ∧ x ∈ R.cell σ) :
    R.carrier x ∈ S.cells ∧ x ∈ R.cell (R.carrier x) := by
  rw [carrier, dif_pos h]
  exact h.choose_spec

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

 
theorem cell_subset_domain (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) : R.cell σ ⊆ D := by
  rw [← h.iUnion_eq]
  exact Set.subset_biUnion_of_mem hσ

 
theorem exists_cell (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    ∃ σ, σ ∈ S.cells ∧ x ∈ R.cell σ := by
  rw [← h.iUnion_eq] at hx
  obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hx
  exact ⟨σ, hσ, hxσ⟩

theorem mem_cells_carrier [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    R.carrier x ∈ S.cells := (R.carrier_spec x (h.exists_cell hx)).1

theorem mem_cell_carrier [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    x ∈ R.cell (R.carrier x) := (R.carrier_spec x (h.exists_cell hx)).2

 


theorem carrier_eq [Nonempty γ] (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells)
    (hx : x ∈ R.cell σ) : R.carrier x = σ := by
  have hxD : x ∈ D := h.cell_subset_domain hσ hx
  by_contra hne
  exact Set.disjoint_left.1 (h.disjoint (h.mem_cells_carrier hxD) hσ hne)
    (h.mem_cell_carrier hxD) hx

 
theorem mem_star_carrier [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    x ∈ R.star (R.carrier x) :=
  closure_cell_subset_star (h.sub_refl (h.mem_cells_carrier hx))
    (_root_.subset_closure (h.mem_cell_carrier hx))

theorem star_nonempty (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) : (R.star σ).Nonempty := by
  obtain ⟨z, hz⟩ := h.nonempty hσ
  exact ⟨z, closure_cell_subset_star (h.sub_refl hσ) (_root_.subset_closure hz)⟩

 
theorem star_subset_closure_domain (h : R.IsCellDecomposition D) (hS : S.CombInvariants) :
    R.star σ ⊆ closure D := by
  intro y hy
  obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
  exact closure_mono (h.cell_subset_domain (hS.sub_mem_right hτ)) hyτ

theorem isBounded_star (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) : IsBounded (R.star σ) :=
  hD.closure.subset (h.star_subset_closure_domain hS)

 

theorem isCompact_star (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) : IsCompact (R.star σ) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_star hS) (h.isBounded_star hS hD)

 

theorem star_anti_of_sub (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hσ : σ ∈ S.cells) (hρ : ρ ∈ S.cells) (hsub : S.sub σ ρ) : R.star ρ ⊆ R.star σ := by
  intro y hy
  obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
  exact mem_star_iff.2 ⟨τ, h.sub_trans hσ hρ (hS.sub_mem_right hτ) hsub hτ, hyτ⟩

end IsCellDecomposition

 




 






structure Refines {S' S : CellStructure γ} (R' : S'.Realization) (R : S.Realization)
    (par : γ → γ) : Prop where
   
  parent_mem_cells : ∀ ⦃σ⦄, σ ∈ S'.cells → par σ ∈ S.cells
   
  parent_mem_faces : ∀ ⦃F⦄, F ∈ S'.faces → par F ∈ S.faces
   
  sub_parent : ∀ ⦃σ τ⦄, S'.sub σ τ → S.sub (par σ) (par τ)
   
  cell_subset : ∀ ⦃σ⦄, σ ∈ S'.cells → R'.cell σ ⊆ R.cell (par σ)

namespace Refines

variable {S' S'' : CellStructure γ} {R : S.Realization} {R' : S'.Realization}
  {R'' : S''.Realization} {par par' : γ → γ} {D' : Set Plane}

 

theorem refl (R : S.Realization) : R.Refines R id where
  parent_mem_cells := fun _ hσ => hσ
  parent_mem_faces := fun _ hF => hF
  sub_parent := fun _ _ h => h
  cell_subset := fun _ _ => subset_rfl

 


theorem trans (h' : R''.Refines R' par') (h : R'.Refines R par) : R''.Refines R (par ∘ par') where
  parent_mem_cells := fun _ hσ => h.parent_mem_cells (h'.parent_mem_cells hσ)
  parent_mem_faces := fun _ hF => h.parent_mem_faces (h'.parent_mem_faces hF)
  sub_parent := fun _ _ hst => h.sub_parent (h'.sub_parent hst)
  cell_subset := fun _ hσ => (h'.cell_subset hσ).trans (h.cell_subset (h'.parent_mem_cells hσ))

 
theorem closure_cell_subset (h : R'.Refines R par) {σ : γ} (hσ : σ ∈ S'.cells) :
    closure (R'.cell σ) ⊆ closure (R.cell (par σ)) :=
  closure_mono (h.cell_subset hσ)

 

theorem parent_carrier [Nonempty γ] (href : R'.Refines R par) (h : R.IsCellDecomposition D)
    (h' : R'.IsCellDecomposition D') {x : Plane} (hx : x ∈ D') :
    par (R'.carrier x) = R.carrier x :=
  (h.carrier_eq (href.parent_mem_cells (h'.mem_cells_carrier hx))
    (href.cell_subset (h'.mem_cells_carrier hx) (h'.mem_cell_carrier hx))).symm

 

theorem star_subset (href : R'.Refines R par) (hS' : S'.CombInvariants) {σ : γ} :
    R'.star σ ⊆ R.star (par σ) := by
  intro y hy
  obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
  exact closure_cell_subset_star (href.sub_parent hτ)
    (href.closure_cell_subset (hS'.sub_mem_right hτ) hyτ)

 

theorem star_carrier_subset [Nonempty γ] (href : R'.Refines R par) (hS' : S'.CombInvariants)
    (h : R.IsCellDecomposition D) (h' : R'.IsCellDecomposition D') {x : Plane} (hx : x ∈ D') :
    R'.star (R'.carrier x) ⊆ R.star (R.carrier x) := by
  rw [← href.parent_carrier h h' hx]
  exact href.star_subset hS'

end Refines

 






namespace Refines

variable {S' : CellStructure γ} {R₁ R₂ : S.Realization} {R₁' R₂' : S'.Realization} {par : γ → γ}
  {D₁ D₂ D₁' D₂' : Set Plane}

 


theorem carrier_congr [Nonempty γ] (h₁ : R₁'.Refines R₁ par) (h₂ : R₂'.Refines R₂ par)
    (hd₁ : R₁.IsCellDecomposition D₁) (hd₁' : R₁'.IsCellDecomposition D₁')
    (hd₂ : R₂.IsCellDecomposition D₂) (hd₂' : R₂'.IsCellDecomposition D₂')
    {x y : Plane} (hx : x ∈ D₁') (hy : y ∈ D₂')
    (hxy : R₁'.carrier x = R₂'.carrier y) : R₁.carrier x = R₂.carrier y := by
  rw [← h₁.parent_carrier hd₁ hd₁' hx, ← h₂.parent_carrier hd₂ hd₂' hy, hxy]

 





theorem target_star_subset [Nonempty γ] (h₁ : R₁'.Refines R₁ par) (h₂ : R₂'.Refines R₂ par)
    (hS' : S'.CombInvariants) (hd₁ : R₁.IsCellDecomposition D₁)
    (hd₁' : R₁'.IsCellDecomposition D₁') {x : Plane} (hx : x ∈ D₁') :
    R₂'.star (R₁'.carrier x) ⊆ R₂.star (R₁.carrier x) := by
  rw [← h₁.parent_carrier hd₁ hd₁' hx]
  exact h₂.star_subset hS'

end Refines

 

 

theorem star_inter_nonempty_of_star_inter_nonempty {R₁ R₂ : S.Realization} {D₁ D₂ : Set Plane}
    (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂) (hS : S.CombInvariants)
    {σ τ : γ} (hne : (R₁.star σ ∩ R₁.star τ).Nonempty) : (R₂.star σ ∩ R₂.star τ).Nonempty := by
  obtain ⟨p, hpσ, hpτ⟩ := hne
  obtain ⟨α, hσα, hpα⟩ := mem_star_iff.1 hpσ
  obtain ⟨β, hτβ, hpβ⟩ := mem_star_iff.1 hpτ
  have hα : α ∈ S.cells := hS.sub_mem_right hσα
  have hβ : β ∈ S.cells := hS.sub_mem_right hτβ
  
  rw [h₁.closure_eq hα] at hpα
  obtain ⟨ρ, ⟨hρ, hρα⟩, hpρ⟩ := Set.mem_iUnion₂.1 hpα
  have hρβ : S.sub ρ β := h₁.sub_of_mem hρ hβ hpρ hpβ
  
  obtain ⟨w, hw⟩ := h₂.nonempty hρ
  exact ⟨w, closure_cell_subset_star hσα (h₂.subset_closure hρ hα hρα hw),
    closure_cell_subset_star hτβ (h₂.subset_closure hρ hβ hρβ hw)⟩

 

theorem star_inter_nonempty_congr {R₁ R₂ : S.Realization} {D₁ D₂ : Set Plane}
    (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂) (hS : S.CombInvariants)
    {σ τ : γ} : (R₁.star σ ∩ R₁.star τ).Nonempty ↔ (R₂.star σ ∩ R₂.star τ).Nonempty :=
  ⟨star_inter_nonempty_of_star_inter_nonempty h₁ h₂ hS,
    star_inter_nonempty_of_star_inter_nonempty h₂ h₁ hS⟩

 

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ : γ} {x y : Plane} {η : ℝ}

 


theorem star_eq_faces (h : R.IsCellDecomposition D) (hS : S.CombInvariants) (hσ : σ ∈ S.cells) :
    R.star σ = ⋃ F ∈ {F | F ∈ S.faces ∧ S.sub σ F}, closure (R.cell F) := by
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
    have hτc : τ ∈ S.cells := hS.sub_mem_right hτ
    obtain ⟨F, hF, hτF⟩ := hS.mem_face hτc
    have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
    refine Set.mem_iUnion₂.2 ⟨F, ⟨hF, h.sub_trans hσ hτc hFc hτ hτF⟩, ?_⟩
    exact closure_minimal (h.subset_closure hτc hFc hτF) isClosed_closure hyτ
  · exact Set.iUnion₂_subset fun _ hF => closure_cell_subset_star hF.2

 
theorem mem_closure_face (h : R.IsCellDecomposition D) {F : γ} (hσ : σ ∈ S.cells)
    (hF : F ∈ S.faces) (hsub : S.sub σ F) (hx : x ∈ R.cell σ) : x ∈ closure (R.cell F) :=
  h.subset_closure hσ (S.mem_cells_of_mem_faces hF) hsub hx

 

theorem dist_le_of_mem_star (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) (hσ : σ ∈ S.cells)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub σ F → diam (closure (R.cell F)) ≤ η)
    (hx : x ∈ R.cell σ) (hy : y ∈ R.star σ) : dist x y ≤ η := by
  rw [h.star_eq_faces hS hσ] at hy
  obtain ⟨F, ⟨hF, hsub⟩, hyF⟩ := Set.mem_iUnion₂.1 hy
  have hbdd : IsBounded (closure (R.cell F)) :=
    (hD.subset (h.cell_subset_domain (S.mem_cells_of_mem_faces hF))).closure
  exact le_trans (dist_le_diam_of_mem hbdd (h.mem_closure_face hσ hF hsub hx) hyF) (hdiam hF hsub)

 

theorem diam_star_le (h : R.IsCellDecomposition D) (hS : S.CombInvariants) (hD : IsBounded D)
    (hσ : σ ∈ S.cells)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub σ F → diam (closure (R.cell F)) ≤ η) :
    diam (R.star σ) ≤ 2 * η := by
  obtain ⟨x, hx⟩ := h.nonempty hσ
  obtain ⟨F, hF, hσF⟩ := hS.mem_face hσ
  have hη : 0 ≤ η := le_trans diam_nonneg (hdiam hF hσF)
  refine diam_le_of_forall_dist_le (by linarith) fun y hy z hz => ?_
  have hxy : dist x y ≤ η := h.dist_le_of_mem_star hS hD hσ hdiam hx hy
  have hxz : dist x z ≤ η := h.dist_le_of_mem_star hS hD hσ hdiam hx hz
  calc dist y z ≤ dist y x + dist x z := dist_triangle y x z
    _ = dist x y + dist x z := by rw [dist_comm y x]
    _ ≤ 2 * η := by linarith

 




theorem diam_star_lt (h : R.IsCellDecomposition D) (hS : S.CombInvariants) (hD : IsBounded D)
    (hσ : σ ∈ S.cells)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub σ F → diam (closure (R.cell F)) < η) :
    diam (R.star σ) < 2 * η := by
  classical
  have hfin : {F | F ∈ S.faces ∧ S.sub σ F}.Finite := S.finite_faces.subset fun _ hF => hF.1
  have hne : {F | F ∈ S.faces ∧ S.sub σ F}.Nonempty := by
    obtain ⟨F, hF, hσF⟩ := hS.mem_face hσ
    exact ⟨F, hF, hσF⟩
  obtain ⟨F₀, hF₀, hmax⟩ := Finset.exists_max_image hfin.toFinset
    (fun F => diam (closure (R.cell F))) (hfin.toFinset_nonempty.2 hne)
  rw [Set.Finite.mem_toFinset] at hF₀
  have hle : diam (R.star σ) ≤ 2 * diam (closure (R.cell F₀)) :=
    h.diam_star_le hS hD hσ fun F hF hsub =>
      hmax F (Set.Finite.mem_toFinset hfin |>.2 ⟨hF, hsub⟩)
  exact lt_of_le_of_lt hle (by have := hdiam hF₀.1 hF₀.2; linarith)

 
theorem diam_star_carrier_lt [Nonempty γ] (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) (hx : x ∈ D)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub (R.carrier x) F → diam (closure (R.cell F)) < η) :
    diam (R.star (R.carrier x)) < 2 * η :=
  h.diam_star_lt hS hD (h.mem_cells_carrier hx) hdiam

end IsCellDecomposition

namespace Refines

variable {S' : CellStructure γ} {R : S.Realization} {R' : S'.Realization} {par : γ → γ}
  {D : Set Plane} {η : ℝ}

 

theorem diam_cell_le (href : R'.Refines R par) (h : R.IsCellDecomposition D) (hD : IsBounded D)
    {F : γ} (hF : F ∈ S'.cells) :
    diam (closure (R'.cell F)) ≤ diam (closure (R.cell (par F))) :=
  diam_mono (href.closure_cell_subset hF)
    ((hD.subset (h.cell_subset_domain (href.parent_mem_cells hF))).closure)

 

theorem diam_cell_le_of_forall (href : R'.Refines R par) (h : R.IsCellDecomposition D)
    (hD : IsBounded D) (hdiam : ∀ ⦃F⦄, F ∈ S.faces → diam (closure (R.cell F)) ≤ η)
    {F : γ} (hF : F ∈ S'.faces) : diam (closure (R'.cell F)) ≤ η :=
  le_trans (href.diam_cell_le h hD (S'.mem_cells_of_mem_faces hF))
    (hdiam (href.parent_mem_faces hF))

end Refines

 

 


def cellNbhd (R : S.Realization) (x : Plane) : Set Plane :=
  (⋃ τ ∈ {τ | τ ∈ S.cells ∧ x ∉ closure (R.cell τ)}, closure (R.cell τ))ᶜ

theorem isOpen_cellNbhd (R : S.Realization) (x : Plane) : IsOpen (R.cellNbhd x) :=
  ((S.finite_cells.subset fun _ hτ => hτ.1).isClosed_biUnion
    fun _ _ => isClosed_closure).isOpen_compl

theorem mem_cellNbhd_self (R : S.Realization) (x : Plane) : x ∈ R.cellNbhd x := by
  intro hx
  obtain ⟨τ, hτ, hxτ⟩ := Set.mem_iUnion₂.1 hx
  exact hτ.2 hxτ

theorem cellNbhd_mem_nhds (R : S.Realization) (x : Plane) : R.cellNbhd x ∈ nhds x :=
  (isOpen_cellNbhd R x).mem_nhds (mem_cellNbhd_self R x)

 
theorem mem_closure_of_mem_cellNbhd {R : S.Realization} {x z : Plane} {τ : γ} (hτ : τ ∈ S.cells)
    (hz : z ∈ R.cellNbhd x) (hzτ : z ∈ closure (R.cell τ)) : x ∈ closure (R.cell τ) := by
  by_contra hx
  exact hz (Set.mem_iUnion₂.2 ⟨τ, ⟨hτ, hx⟩, hzτ⟩)

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {x z : Plane}

 

theorem sub_carrier_of_mem_cellNbhd [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D)
    (hz : z ∈ R.cellNbhd x) (hzD : z ∈ D) : S.sub (R.carrier x) (R.carrier z) := by
  have hxclos : x ∈ closure (R.cell (R.carrier z)) :=
    mem_closure_of_mem_cellNbhd (h.mem_cells_carrier hzD) hz
      (_root_.subset_closure (h.mem_cell_carrier hzD))
  exact h.sub_of_mem (h.mem_cells_carrier hx) (h.mem_cells_carrier hzD)
    (h.mem_cell_carrier hx) hxclos

 







theorem cell_neighborhood [Nonempty γ] (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hx : x ∈ D) (hz : z ∈ R.cellNbhd x) (hzD : z ∈ D) :
    S.sub (R.carrier x) (R.carrier z) ∧ R.star (R.carrier z) ⊆ R.star (R.carrier x) := by
  have hsub := h.sub_carrier_of_mem_cellNbhd hx hz hzD
  exact ⟨hsub, h.star_anti_of_sub hS (h.mem_cells_carrier hx) (h.mem_cells_carrier hzD) hsub⟩

end IsCellDecomposition

 






 

theorem pos_pair_subset_edgeArc (R : S.Realization) {e a b : γ} (hl : S.skel.IsLink e a b) :
    ({R.pos a, R.pos b} : Set Plane) ⊆ Graph.edgeArc R.drawing e := by
  obtain ⟨-, -, hlink⟩ := R.isDrawing.edge_param (by rw [Graph.edgeSet_map]; exact hl.edge_mem)
  have h0 : R.drawing e 0 ∈ Graph.edgeArc R.drawing e := Set.mem_image_of_mem _ zero_mem_I
  have h1 : R.drawing e 1 ∈ Graph.edgeArc R.drawing e := Set.mem_image_of_mem _ one_mem_I
  have hpair : ({R.pos a, R.pos b} : Set Plane) = {R.drawing e 0, R.drawing e 1} := by
    rcases (hl.map R.pos).eq_and_eq_or_eq_and_eq hlink with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb]; exact Set.pair_comm _ _
  rw [hpair]
  rintro z (rfl | rfl)
  exacts [h0, h1]

end Realization

namespace SkeletonHomeo

variable {R₁ R₂ : S.Realization} {D₁ D₂ : Set Plane} {σ : γ} {x : Plane}

 



theorem image_cell (g : SkeletonHomeo R₁ R₂) (hσ : σ ∈ V(S.skel) ∪ E(S.skel)) :
    g.toFun '' R₁.cell σ = R₂.cell σ := by
  rcases hσ with hv | he
  · rw [R₁.cell_vertex hv, R₂.cell_vertex hv, Set.image_singleton, g.pos_apply hv]
  · obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
    have harc : Graph.edgeArc R₁.drawing σ ⊆ R₁.skeletonSet :=
      Graph.edgeArc_subset_pointSet (by rw [Realization.edgeSet_graph]; exact he)
    rw [R₁.cell_edge hl, R₂.cell_edge hl,
      (g.injOn.mono harc).image_sdiff_subset (R₁.pos_pair_subset_edgeArc hl),
      g.edgeArc_image he, Set.image_pair, g.pos_apply hl.left_mem, g.pos_apply hl.right_mem]

 

theorem carrier_congr [Nonempty γ] (g : SkeletonHomeo R₁ R₂) (h₁ : R₁.IsCellDecomposition D₁)
    (h₂ : R₂.IsCellDecomposition D₂) (hσ : σ ∈ V(S.skel) ∪ E(S.skel)) (hx : x ∈ R₁.cell σ) :
    R₂.carrier (g.toFun x) = R₁.carrier x := by
  have hcells : σ ∈ S.cells := by
    rcases hσ with hv | he
    exacts [S.mem_cells_of_mem_vertexSet hv, S.mem_cells_of_mem_edgeSet he]
  have hgx : g.toFun x ∈ R₂.cell σ := by
    rw [← g.image_cell hσ]; exact Set.mem_image_of_mem _ hx
  rw [h₁.carrier_eq hcells hx, h₂.carrier_eq hcells hgx]

end SkeletonHomeo

 







variable {S' : CellStructure γ} {R : S.Realization} {R' : S'.Realization} {par : γ → γ}
  {c : γ} {N : Set γ} {D : Set Plane}

 



theorem refines_of_elementary (hc : c ∈ S.cells) (hcells : S'.cells = (S.cells \ {c}) ∪ N)
    (hfresh : ∀ ⦃σ⦄, σ ∈ N → σ ∉ S.cells) (hpar_new : ∀ ⦃σ⦄, σ ∈ N → par σ = c)
    (hpar_old : ∀ ⦃σ⦄, σ ∈ S.cells → par σ = σ)
    (hfaces : ∀ ⦃F⦄, F ∈ S'.faces → par F ∈ S.faces)
    (hsub : ∀ ⦃σ τ⦄, S'.sub σ τ → S.sub (par σ) (par τ))
    (hcell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ c → R'.cell σ = R.cell σ)
    (h : R.IsCellDecomposition D) (h' : R'.IsCellDecomposition D) : R'.Refines R par where
  parent_mem_cells := by
    intro σ hσ
    rw [hcells] at hσ
    rcases hσ with ⟨hσc, -⟩ | hσN
    · rw [hpar_old hσc]; exact hσc
    · rw [hpar_new hσN]; exact hc
  parent_mem_faces := hfaces
  sub_parent := hsub
  cell_subset := by
    intro σ hσ
    have hσ' := hσ
    rw [hcells] at hσ'
    rcases hσ' with ⟨hσc, hσne⟩ | hσN
    · rw [hpar_old hσc, hcell_eq hσc hσne]
    · rw [hpar_new hσN]
      intro w hw
      
      
      obtain ⟨ρ, hρ, hwρ⟩ := h.exists_cell (h'.cell_subset_domain hσ hw)
      by_cases hρc : ρ = c
      · exact hρc ▸ hwρ
      · have hρ' : ρ ∈ S'.cells := by rw [hcells]; exact Or.inl ⟨hρ, hρc⟩
        have hne : σ ≠ ρ := by rintro rfl; exact hfresh hσN hρ
        have hwρ' : w ∈ R'.cell ρ := by rw [hcell_eq hρ hρc]; exact hwρ
        exact absurd hwρ' (Set.disjoint_left.1 (h'.disjoint hσ hρ' hne) hw)

namespace SubdivData

variable {d : S.SubdivData}

 

theorem IsRefinement.refines (hS : S.CombInvariants) {R : S.Realization}
    {R' : (S.subdivideEdge d).Realization} (href : d.IsRefinement R R') :
    R'.Refines R d.parent where
  parent_mem_cells := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσc, -⟩ | hσN
    · rw [d.parent_of_mem_cells hσc]; exact hσc
    · rw [d.parent_of_mem_newCells hσN]; exact d.edge_mem_cells
  parent_mem_faces := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    rw [d.parent_of_mem_cells (S.mem_cells_of_mem_faces hF)]
    exact hF
  sub_parent := fun _ _ h => d.sub_parent hS h
  cell_subset := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσc, hσe⟩ | hσN
    · rw [d.parent_of_mem_cells hσc, href.cell_eq hσc hσe]
    · rw [d.parent_of_mem_newCells hσN]; exact href.cell_subset_edge hσN

end SubdivData

namespace SplitData

variable {d : S.SplitData}

 


theorem refines (hS : S.CombInvariants) {R : S.Realization}
    {R' : (S.splitFace d).Realization} {D : Set Plane} (h : R.IsCellDecomposition D)
    (h' : R'.IsCellDecomposition D)
    (hcell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ d.face → R'.cell σ = R.cell σ) :
    R'.Refines R d.parent := by
  refine refines_of_elementary d.face_mem_cells (splitFace_cells d)
    (fun _ hσ => notMem_cells_of_mem_newCells hσ) (fun _ hσ => d.parent_of_mem_newCells hσ)
    (fun _ hσ => d.parent_of_mem_cells hσ) ?_ (fun _ _ h => d.sub_parent hS h) hcell_eq h h'
  intro F hF
  rw [splitFace_faces] at hF
  rcases hF with rfl | rfl | ⟨hFc, -⟩
  · rw [d.parent_of_mem_newCells d.face₁_mem_newCells]; exact d.face_mem
  · rw [d.parent_of_mem_newCells d.face₂_mem_newCells]; exact d.face_mem
  · rw [d.parent_of_mem_cells (S.mem_cells_of_mem_faces hFc)]; exact hFc

end SplitData

 







example {γ : Type*} [Nonempty γ] (St : ℕ → CellStructure γ)
    (R : ∀ n, (St n).Realization) (R' : ∀ n, (St n).Realization)
    (par : ℕ → γ → γ) (D D' : Set Plane) (hD' : IsBounded D')
    (hd : ∀ n, (R n).IsCellDecomposition D) (hd' : ∀ n, (R' n).IsCellDecomposition D')
    (hcomb : ∀ n, (St n).CombInvariants)
    (href : ∀ n, (R (n + 1)).Refines (R n) (par n))
    (href' : ∀ n, (R' (n + 1)).Refines (R' n) (par n))
    (η : ℕ → ℝ) (x : Plane) (hx : x ∈ D)
    (hmesh : ∀ n, ∀ ⦃F : γ⦄, F ∈ (St n).faces → (St n).sub ((R n).carrier x) F →
      diam (closure ((R' n).cell F)) < η n) :
    (∀ n, (R' (n + 1)).star ((R (n + 1)).carrier x) ⊆ (R' n).star ((R n).carrier x)) ∧
      (∀ n, ((R' n).star ((R n).carrier x)).Nonempty) ∧
      (∀ n, IsCompact ((R' n).star ((R n).carrier x))) ∧
      (∀ n, diam ((R' n).star ((R n).carrier x)) < 2 * η n) :=
  ⟨fun n => (href n).target_star_subset (href' n) (hcomb (n + 1)) (hd n) (hd (n + 1)) hx,
    fun n => (hd' n).star_nonempty ((hd n).mem_cells_carrier hx),
    fun n => (hd' n).isCompact_star (hcomb n) hD',
    fun n => (hd' n).diam_star_lt (hcomb n) hD' ((hd n).mem_cells_carrier hx) (hmesh n)⟩

end CellStructure

end Schoenflies
