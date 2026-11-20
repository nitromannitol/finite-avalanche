/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/CellulationInvariants.lean.
-/
import FiniteAvalanches.Support.Schoenflies.RefinementStars
import FiniteAvalanches.Support.Schoenflies.JordanClosed

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 






















































































open Set Bornology
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

 
def subcells (S : CellStructure γ) (τ : γ) : Set γ := {σ | σ ∈ S.cells ∧ S.sub σ τ}

theorem mem_subcells_iff {σ τ : γ} : σ ∈ S.subcells τ ↔ σ ∈ S.cells ∧ S.sub σ τ := Iff.rfl

theorem subcells_subset_cells {τ : γ} : S.subcells τ ⊆ S.cells := fun _ h => h.1

namespace Realization

variable {R : S.Realization} {D : Set Plane} {F T σ τ : γ}

 





 
def cellUnion (R : S.Realization) (Cs : Set γ) : Set Plane := ⋃ σ ∈ Cs, R.cell σ

theorem mem_cellUnion_iff {Cs : Set γ} {z : Plane} :
    z ∈ R.cellUnion Cs ↔ ∃ σ ∈ Cs, z ∈ R.cell σ := by
  simp only [cellUnion, Set.mem_iUnion, exists_prop]

theorem cellUnion_mono {Cs Ds : Set γ} (h : Cs ⊆ Ds) : R.cellUnion Cs ⊆ R.cellUnion Ds :=
  Set.biUnion_subset_biUnion_left h

theorem cell_subset_cellUnion {Cs : Set γ} (h : σ ∈ Cs) : R.cell σ ⊆ R.cellUnion Cs :=
  Set.subset_biUnion_of_mem (u := fun ρ => R.cell ρ) h

theorem cellUnion_union (R : S.Realization) (Cs Ds : Set γ) :
    R.cellUnion (Cs ∪ Ds) = R.cellUnion Cs ∪ R.cellUnion Ds := Set.biUnion_union _ _ _

theorem cellUnion_insert (R : S.Realization) (σ : γ) (Cs : Set γ) :
    R.cellUnion (insert σ Cs) = R.cell σ ∪ R.cellUnion Cs := Set.biUnion_insert _ _ _

@[simp] theorem cellUnion_empty (R : S.Realization) : R.cellUnion ∅ = ∅ := Set.biUnion_empty _

@[simp] theorem cellUnion_singleton (R : S.Realization) (σ : γ) :
    R.cellUnion {σ} = R.cell σ := Set.biUnion_singleton _ _

theorem cellUnion_pair (R : S.Realization) (σ τ : γ) :
    R.cellUnion {σ, τ} = R.cell σ ∪ R.cell τ := Set.biUnion_pair _ _ _

theorem cellUnion_subset {Cs : Set γ} {A : Set Plane} (h : ∀ σ ∈ Cs, R.cell σ ⊆ A) :
    R.cellUnion Cs ⊆ A := Set.iUnion₂_subset h

 

theorem cellUnion_congr {S₁ S₂ : CellStructure γ} {R₁ : S₁.Realization} {R₂ : S₂.Realization}
    {Cs : Set γ} (h : ∀ σ ∈ Cs, R₁.cell σ = R₂.cell σ) : R₁.cellUnion Cs = R₂.cellUnion Cs :=
  Set.iUnion₂_congr h

 



def faceBoundary (R : S.Realization) (F : γ) : Set Plane := R.cellUnion (S.subcells F \ {F})

namespace IsCellDecomposition

 
theorem closure_cell_eq (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    closure (R.cell τ) = R.cellUnion (S.subcells τ) := h.closure_eq hτ

theorem mem_subcells_self (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) : τ ∈ S.subcells τ :=
  ⟨hτ, h.sub_refl hτ⟩

 
theorem closure_cell_eq_union (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    closure (R.cell τ) = R.cell τ ∪ R.faceBoundary τ := by
  rw [h.closure_cell_eq hτ, faceBoundary, ← R.cellUnion_insert,
    Set.insert_sdiff_singleton, Set.insert_eq_self.2 (h.mem_subcells_self hτ)]

 
theorem disjoint_faceBoundary (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    Disjoint (R.cell τ) (R.faceBoundary τ) := by
  refine Set.disjoint_left.2 fun z hz hz' => ?_
  obtain ⟨σ, ⟨⟨hσ, -⟩, hσne⟩, hzσ⟩ := mem_cellUnion_iff.1 hz'
  exact Set.disjoint_left.1 (h.disjoint hτ hσ (Ne.symm hσne)) hz hzσ

 


theorem faceBoundary_eq_frontier (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells)
    (hopen : IsOpen (R.cell τ)) : R.faceBoundary τ = frontier (R.cell τ) := by
  rw [hopen.frontier_eq, h.closure_cell_eq_union hτ, Set.union_sdiff_left,
    sdiff_eq_left.2 (h.disjoint_faceBoundary hτ).symm]

end IsCellDecomposition

 








 






structure IsFaceJordan (R : S.Realization) : Prop where
   
  isJordanCurve : ∀ ⦃F⦄, F ∈ S.faces → IsJordanCurve (frontier (R.cell F))
   
  cell_eq_inside : ∀ ⦃F⦄, F ∈ S.faces → R.cell F = inside (frontier (R.cell F))

namespace IsFaceJordan

 

theorem isSeparating (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) :
    IsSeparating (frontier (R.cell F)) :=
  jordan_curve_theorem (hJ.isJordanCurve hF)

 

theorem isOpen (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : IsOpen (R.cell F) := by
  rw [hJ.cell_eq_inside hF]
  exact (hJ.isSeparating hF).isOpen_inside

theorem isConnected (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : IsConnected (R.cell F) := by
  rw [hJ.cell_eq_inside hF]
  exact (hJ.isSeparating hF).isConnected_inside

theorem isBounded (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : IsBounded (R.cell F) := by
  rw [hJ.cell_eq_inside hF]
  exact (hJ.isSeparating hF).isBounded_inside

theorem nonempty (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : (R.cell F).Nonempty :=
  (hJ.isConnected hF).nonempty

 

theorem isCompact_closure (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) :
    IsCompact (closure (R.cell F)) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure (hJ.isBounded hF).closure

 

theorem faceBoundary_eq (hJ : R.IsFaceJordan) (h : R.IsCellDecomposition D) (hF : F ∈ S.faces) :
    R.faceBoundary F = frontier (R.cell F) :=
  h.faceBoundary_eq_frontier (S.mem_cells_of_mem_faces hF) (hJ.isOpen hF)

theorem isJordanCurve_faceBoundary (hJ : R.IsFaceJordan) (h : R.IsCellDecomposition D)
    (hF : F ∈ S.faces) : IsJordanCurve (R.faceBoundary F) := by
  rw [hJ.faceBoundary_eq h hF]; exact hJ.isJordanCurve hF

theorem cell_eq_inside_faceBoundary (hJ : R.IsFaceJordan) (h : R.IsCellDecomposition D)
    (hF : F ∈ S.faces) : R.cell F = inside (R.faceBoundary F) := by
  rw [hJ.faceBoundary_eq h hF]; exact hJ.cell_eq_inside hF

end IsFaceJordan

namespace IsCellDecomposition

 


theorem face_eq_of_isFaceJordan (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan)
    (hF : F ∈ S.faces) (hT : T ∈ S.faces) (hsub : R.cell F ⊆ closure (R.cell T)) : F = T :=
  h.face_eq hF hT (hJ.isOpen hF) hsub

 
theorem sub_face_eq (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan)
    (hF : F ∈ S.faces) (hT : T ∈ S.faces) (hsub : S.sub F T) : F = T :=
  h.face_eq_of_isFaceJordan hJ hF hT
    (h.subset_closure (S.mem_cells_of_mem_faces hF) (S.mem_cells_of_mem_faces hT) hsub)

end IsCellDecomposition

end Realization

 





namespace SubdivData

variable {d : S.SubdivData} {R : S.Realization} {R' : (S.subdivideEdge d).Realization} {F : γ}

theorem IsRefinement.cell_face_eq (href : d.IsRefinement R R') (hF : F ∈ S.faces) :
    R'.cell F = R.cell F :=
  href.cell_eq (S.mem_cells_of_mem_faces hF) (S.faces_ne_edgeSet hF d.edge_mem_edgeSet)

 
theorem IsRefinement.isFaceJordan (href : d.IsRefinement R R') (hJ : R.IsFaceJordan) :
    R'.IsFaceJordan where
  isJordanCurve := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    rw [href.cell_face_eq hF]
    exact hJ.isJordanCurve hF
  cell_eq_inside := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    rw [href.cell_face_eq hF]
    exact hJ.cell_eq_inside hF

 



theorem IsRefinement.isCellDecomposition_and_isFaceJordan (hS : S.CombInvariants)
    (href : d.IsRefinement R R') {D : Set Plane} (h : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    R'.IsCellDecomposition D ∧ R'.IsFaceJordan ∧ R'.Refines R d.parent :=
  ⟨href.isCellDecomposition hS h, href.isFaceJordan hJ, href.refines hS⟩

 






 
theorem exists_substWalk (d : S.SubdivData) {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    ∃ W', d.SubstWalk u W W' := by
  induction h with
  | nil hx => exact ⟨[], .nil _⟩
  | @cons a w b f W hl _ ih =>
    obtain ⟨W', hW'⟩ := ih
    by_cases hf : f = d.edge
    · subst hf
      rcases d.isLink.eq_and_eq_or_eq_and_eq hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · subst h₁; subst h₂; exact ⟨_, .forward hW'⟩
      · subst h₁; subst h₂; exact ⟨_, .backward hW'⟩
    · exact ⟨_, .other hl hf hW'⟩

theorem newVertex_mem_skeleton_vertexSet (d : S.SubdivData) :
    d.newVertex ∈ V(d.skeleton) := by
  rw [d.skeleton_vertexSet]; exact Set.mem_insert _ _

 
theorem SubstWalk.isWalk {d : S.SubdivData} {u v : γ} {W W' : List γ}
    (hsub : d.SubstWalk u W W') (h : S.skel.IsWalk u W v) : d.skeleton.IsWalk u W' v := by
  induction hsub generalizing v with
  | nil u =>
    cases h with
    | nil hx =>
      exact .nil (by rw [d.skeleton_vertexSet]; exact Set.mem_insert_of_mem _ hx)
  | forward hs ih =>
    cases h with
    | cons hl hW =>
      have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      exact .cons hlink₁ (.cons hlink₂ (ih (d.isLink.right_unique hl ▸ hW)))
  | backward hs ih =>
    cases h with
    | cons hl hW =>
      have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
      have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
      exact .cons hlink₂ (.cons hlink₁ (ih (d.isLink.symm.right_unique hl ▸ hW)))
  | other hl hf hs ih =>
    cases h with
    | cons hl' hW =>
      have hlink : d.skeleton.IsLink _ _ _ :=
        d.skeleton_isLink.2 (Or.inl ⟨hl, hf,
          fun hh => d.newEdge₁_notMem_edgeSet (hh ▸ hl.edge_mem),
          fun hh => d.newEdge₂_notMem_edgeSet (hh ▸ hl.edge_mem)⟩)
      exact .cons hlink (ih (hl.right_unique hl' ▸ hW))

 

theorem SubstWalk.eq_of_notMem {d : S.SubdivData} {u : γ} {W W' : List γ}
    (hsub : d.SubstWalk u W W') (h : d.edge ∉ W) : W' = W := by
  induction hsub with
  | nil u => rfl
  | forward hs ih => exact absurd (List.mem_cons_self ..) h
  | backward hs ih => exact absurd (List.mem_cons_self ..) h
  | other hl hf hs ih => rw [ih fun hh => h (List.mem_cons_of_mem _ hh)]

 
theorem boundary_isWalk (d : S.SubdivData) {F : γ} (hF : F ∈ S.faces) :
    ∃ u, d.skeleton.IsWalk u ((S.subdivideEdge d).boundary F) u := by
  obtain ⟨u, hW, hsub⟩ := d.boundary_subst hF
  exact ⟨u, SubdivData.SubstWalk.isWalk hsub hW⟩

end SubdivData

 











namespace SplitData

variable {d : S.SplitData} {R : S.Realization} {R' : (S.splitFace d).Realization}

 

def earNewCells (d : S.SplitData) : Set γ := (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear)

theorem newCells_eq (d : S.SplitData) : d.newCells = d.earNewCells ∪ {d.face₁, d.face₂} := rfl

theorem earNewCells_subset_newCells (d : S.SplitData) : d.earNewCells ⊆ d.newCells :=
  Set.subset_union_left

theorem earNewCells_subset_earCells (d : S.SplitData) : d.earNewCells ⊆ d.earCells := by
  rintro z (⟨hz, -⟩ | hz)
  exacts [Or.inl hz, Or.inr hz]

theorem mem_earNewCells_of_mem_ear_vertexSet {z : γ} (hz : z ∈ V(d.ear)) (hs : z ≠ d.source)
    (ht : z ≠ d.target) : z ∈ d.earNewCells :=
  Or.inl ⟨hz, by rintro (h | h); exacts [hs h, ht h]⟩

theorem mem_earNewCells_of_mem_ear_edgeSet {f : γ} (hf : f ∈ E(d.ear)) : f ∈ d.earNewCells :=
  Or.inr hf

theorem mem_splitFace_cells_of_earNew {z : γ} (hz : z ∈ d.earNewCells) :
    z ∈ (S.splitFace d).cells :=
  d.mem_splitFace_cells_of_new (d.earNewCells_subset_newCells hz)

 

 


theorem subRel_iff_of_mem_cells (hS : S.CombInvariants) (d : S.SplitData) {σ τ : γ}
    (hτc : τ ∈ S.cells) (hτf : τ ≠ d.face) :
    d.subRel σ τ ↔ (σ ∈ S.cells ∧ σ ≠ d.face ∧ S.sub σ τ) := by
  refine ⟨fun h => ?_, fun h => d.subRel_of_old h.1 hτc h.2.1 hτf h.2.2⟩
  rcases h with ⟨-, -, hσf, -, hsub⟩ | ⟨heq, hσn⟩ | hinc | ⟨heq, -⟩ | ⟨heq, -⟩
  · exact ⟨hS.sub_mem_left hsub, hσf, hsub⟩
  · exact absurd (heq ▸ hσn) (notMem_newCells_of_mem_cells hτc)
  · exact absurd hτc (d.edge_fresh hinc.edge_mem)
  · exact absurd (heq ▸ hτc) d.face₁_notMem
  · exact absurd (heq ▸ hτc) d.face₂_notMem

 
theorem subcells_of_mem_cells (hS : S.CombInvariants) (d : S.SplitData) {τ : γ}
    (hτc : τ ∈ S.cells) (hτf : τ ≠ d.face) : (S.splitFace d).subcells τ = S.subcells τ := by
  ext σ
  constructor
  · rintro ⟨-, hsub⟩
    obtain ⟨hσc, -, hσ⟩ := (subRel_iff_of_mem_cells hS d hτc hτf).1 hsub
    exact ⟨hσc, hσ⟩
  · rintro ⟨hσc, hσ⟩
    have hσf : σ ≠ d.face := by
      rintro rfl
      exact hτf (hS.face_maximal d.face_mem hσ)
    exact ⟨d.mem_splitFace_cells_of_old hσc hσf,
      (subRel_iff_of_mem_cells hS d hτc hτf).2 ⟨hσc, hσf, hσ⟩⟩

 
theorem subRel_earVertex_iff (d : S.SplitData) {z σ : γ} (hz : z ∈ V(d.ear)) (hs : z ≠ d.source)
    (ht : z ≠ d.target) : d.subRel σ z ↔ σ = z := by
  have hzn : z ∈ d.newCells :=
    d.earNewCells_subset_newCells (mem_earNewCells_of_mem_ear_vertexSet hz hs ht)
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inl ⟨h, h ▸ hzn⟩)⟩
  rcases h with ⟨-, hzn', -, -, -⟩ | ⟨heq, -⟩ | hinc | ⟨heq, -⟩ | ⟨heq, -⟩
  · exact absurd hzn hzn'
  · exact heq
  · exact absurd hinc.edge_mem (Set.disjoint_left.1 d.ear_disjoint hz)
  · exact absurd (heq ▸ hz) fun hh => d.face₁_notMem_ear (Or.inl hh)
  · exact absurd (heq ▸ hz) fun hh => d.face₂_notMem_ear (Or.inl hh)

 
theorem subRel_earEdge_iff (d : S.SplitData) {f a b σ : γ} (hl : d.ear.IsLink f a b) :
    d.subRel σ f ↔ (σ = f ∨ σ = a ∨ σ = b) := by
  have hfn : f ∈ d.newCells :=
    d.earNewCells_subset_newCells (mem_earNewCells_of_mem_ear_edgeSet hl.edge_mem)
  constructor
  · intro h
    rcases h with ⟨-, hfn', -, -, -⟩ | ⟨heq, -⟩ | hinc | ⟨heq, -⟩ | ⟨heq, -⟩
    · exact absurd hfn hfn'
    · exact Or.inl heq
    · exact Or.inr (hinc.eq_or_eq_of_isLink hl)
    · exact absurd (heq ▸ hl.edge_mem) fun hh => d.face₁_notMem_ear (Or.inr hh)
    · exact absurd (heq ▸ hl.edge_mem) fun hh => d.face₂_notMem_ear (Or.inr hh)
  · rintro (rfl | rfl | rfl)
    · exact Or.inr (Or.inl ⟨rfl, hfn⟩)
    · exact Or.inr (Or.inr (Or.inl hl.inc_left))
    · exact Or.inr (Or.inr (Or.inl hl.inc_right))

theorem subcells_earVertex (d : S.SplitData) {z : γ} (hz : z ∈ V(d.ear)) (hs : z ≠ d.source)
    (ht : z ≠ d.target) : (S.splitFace d).subcells z = {z} := by
  ext σ
  refine ⟨fun hσ => (d.subRel_earVertex_iff hz hs ht).1 hσ.2, ?_⟩
  rintro rfl
  exact ⟨d.mem_splitFace_cells_of_earNew (mem_earNewCells_of_mem_ear_vertexSet hz hs ht),
    (d.subRel_earVertex_iff hz hs ht).2 rfl⟩

theorem subcells_earEdge (d : S.SplitData) {f a b : γ} (hl : d.ear.IsLink f a b) :
    (S.splitFace d).subcells f = {f, a, b} := by
  ext σ
  refine ⟨fun hσ => (d.subRel_earEdge_iff hl).1 hσ.2,
    fun hσ => ⟨?_, (d.subRel_earEdge_iff hl).2 hσ⟩⟩
  rcases hσ with rfl | rfl | rfl
  · exact d.mem_splitFace_cells_of_earNew (mem_earNewCells_of_mem_ear_edgeSet hl.edge_mem)
  · exact d.mem_splitFace_cells_of_ear (Or.inl hl.left_mem)
  · exact d.mem_splitFace_cells_of_ear (Or.inl hl.right_mem)

theorem subcells_face₁ (d : S.SplitData) :
    (S.splitFace d).subcells d.face₁ = {d.face₁} ∪ d.earCells ∪ d.cells₁ := by
  ext σ
  constructor
  · intro hσ
    rcases d.subRel_face₁_iff.1 hσ.2 with h | h | h
    exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr h]
  · intro hσ
    have hcell : σ ∈ (S.splitFace d).cells := by
      rcases hσ with (rfl | h) | h
      · exact d.mem_splitFace_cells_of_new d.face₁_mem_newCells
      · exact d.mem_splitFace_cells_of_ear h
      · exact d.mem_splitFace_cells_of_old (d.cells₁_subset h) (d.cells₁_ne_face h)
    refine ⟨hcell, d.subRel_face₁_iff.2 ?_⟩
    rcases hσ with (h | h) | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]

theorem subcells_face₂ (d : S.SplitData) :
    (S.splitFace d).subcells d.face₂ = {d.face₂} ∪ d.earCells ∪ d.cells₂ := by
  ext σ
  constructor
  · intro hσ
    rcases d.subRel_face₂_iff.1 hσ.2 with h | h | h
    exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr h]
  · intro hσ
    have hcell : σ ∈ (S.splitFace d).cells := by
      rcases hσ with (rfl | h) | h
      · exact d.mem_splitFace_cells_of_new d.face₂_mem_newCells
      · exact d.mem_splitFace_cells_of_ear h
      · exact d.mem_splitFace_cells_of_old (d.cells₂_subset h) (d.cells₂_ne_face h)
    refine ⟨hcell, d.subRel_face₂_iff.2 ?_⟩
    rcases hσ with (h | h) | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]

 

 








structure IsRefinement (d : S.SplitData) (R : S.Realization)
    (R' : (S.splitFace d).Realization) : Prop where
   
  cell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ d.face → R'.cell σ = R.cell σ
   
  cell_face : R.cell d.face =
    R'.cell d.face₁ ∪ R'.cell d.face₂ ∪ R'.cellUnion d.earNewCells
   
  nonempty : ∀ ⦃σ⦄, σ ∈ d.newCells → (R'.cell σ).Nonempty
   
  disjoint : ∀ ⦃σ τ⦄, σ ∈ d.newCells → τ ∈ d.newCells → σ ≠ τ → Disjoint (R'.cell σ) (R'.cell τ)
   
  closure_earVertex : ∀ ⦃z⦄, z ∈ V(d.ear) → z ≠ d.source → z ≠ d.target →
    closure (R'.cell z) = R'.cell z
   
  closure_earEdge : ∀ ⦃f a b⦄, d.ear.IsLink f a b →
    closure (R'.cell f) = R'.cell f ∪ (R'.cell a ∪ R'.cell b)
   
  closure_face₁ : closure (R'.cell d.face₁) =
    R'.cell d.face₁ ∪ R'.cellUnion d.earCells ∪ R'.cellUnion d.cells₁
   
  closure_face₂ : closure (R'.cell d.face₂) =
    R'.cell d.face₂ ∪ R'.cellUnion d.earCells ∪ R'.cellUnion d.cells₂

namespace IsRefinement

variable {D : Set Plane}

 
theorem cell_subset_face (href : d.IsRefinement R R') {σ : γ} (hσ : σ ∈ d.newCells) :
    R'.cell σ ⊆ R.cell d.face := by
  rw [href.cell_face]
  rcases hσ with hσ | hσ
  · exact fun _ hz => Or.inr (R'.cell_subset_cellUnion hσ hz)
  · rcases hσ with rfl | rfl
    exacts [fun _ hz => Or.inl (Or.inl hz), fun _ hz => Or.inl (Or.inr hz)]

 
theorem isCellDecomposition (hS : S.CombInvariants) (href : d.IsRefinement R R')
    (h : R.IsCellDecomposition D) : R'.IsCellDecomposition D where
  nonempty := by
    intro σ hσ
    rw [splitFace_cells] at hσ
    rcases hσ with ⟨hσc, hσf⟩ | hσn
    · rw [href.cell_eq hσc hσf]; exact h.nonempty hσc
    · exact href.nonempty hσn
  disjoint := by
    intro σ τ hσ hτ hne
    rw [splitFace_cells] at hσ hτ
    rcases hσ with ⟨hσc, hσf⟩ | hσn <;> rcases hτ with ⟨hτc, hτf⟩ | hτn
    · rw [href.cell_eq hσc hσf, href.cell_eq hτc hτf]; exact h.disjoint hσc hτc hne
    · rw [href.cell_eq hσc hσf]
      exact (h.disjoint hσc d.face_mem_cells hσf).mono_right (href.cell_subset_face hτn)
    · rw [href.cell_eq hτc hτf]
      exact (h.disjoint d.face_mem_cells hτc (Ne.symm hτf)).mono_left
        (href.cell_subset_face hσn)
    · exact href.disjoint hσn hτn hne
  iUnion_eq := by
    rw [← h.iUnion_eq]
    ext z
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨σ, hσ, hz⟩
      rw [splitFace_cells] at hσ
      rcases hσ with ⟨hσc, hσf⟩ | hσn
      · exact ⟨σ, hσc, by rwa [href.cell_eq hσc hσf] at hz⟩
      · exact ⟨d.face, d.face_mem_cells, href.cell_subset_face hσn hz⟩
    · rintro ⟨σ, hσ, hz⟩
      by_cases hσf : σ = d.face
      · subst hσf
        rw [href.cell_face] at hz
        rcases hz with hz | hz
        · rcases hz with hz | hz
          · exact ⟨d.face₁, d.mem_splitFace_cells_of_new d.face₁_mem_newCells, hz⟩
          · exact ⟨d.face₂, d.mem_splitFace_cells_of_new d.face₂_mem_newCells, hz⟩
        · obtain ⟨ρ, hρ, hzρ⟩ := Realization.mem_cellUnion_iff.1 hz
          exact ⟨ρ, d.mem_splitFace_cells_of_earNew hρ, hzρ⟩
      · exact ⟨σ, d.mem_splitFace_cells_of_old hσ hσf, by rwa [href.cell_eq hσ hσf]⟩
  closure_eq := by
    intro τ hτ
    change closure (R'.cell τ) = R'.cellUnion ((S.splitFace d).subcells τ)
    rw [splitFace_cells] at hτ
    rcases hτ with ⟨hτc, hτf⟩ | hτn
    · 
      rw [href.cell_eq hτc hτf, h.closure_cell_eq hτc, d.subcells_of_mem_cells hS hτc hτf]
      refine Set.iUnion₂_congr fun σ hσ => ?_
      refine (href.cell_eq hσ.1 ?_).symm
      rintro rfl
      exact hτf (hS.face_maximal d.face_mem hσ.2)
    · rcases hτn with hτn | hτn
      · rcases hτn with ⟨hzV, hznot⟩ | hfE
        · 
          have hs : τ ≠ d.source := fun hh => hznot (Or.inl hh)
          have ht : τ ≠ d.target := fun hh => hznot (Or.inr hh)
          rw [d.subcells_earVertex hzV hs ht, Realization.cellUnion_singleton,
            href.closure_earVertex hzV hs ht]
        · 
          obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hfE
          rw [d.subcells_earEdge hl, href.closure_earEdge hl, Realization.cellUnion_insert,
            Realization.cellUnion_pair]
      · rcases hτn with rfl | rfl
        · rw [href.closure_face₁, d.subcells_face₁, Realization.cellUnion_union,
            Realization.cellUnion_union, Realization.cellUnion_singleton]
        · rw [href.closure_face₂, d.subcells_face₂, Realization.cellUnion_union,
            Realization.cellUnion_union, Realization.cellUnion_singleton]

 


theorem refines (hS : S.CombInvariants) (href : d.IsRefinement R R')
    (h : R.IsCellDecomposition D) : R'.Refines R d.parent :=
  SplitData.refines hS h (href.isCellDecomposition hS h) href.cell_eq

end IsRefinement

 






 












structure IsCrosscutSplit (d : S.SplitData) (R : S.Realization)
    (R' : (S.splitFace d).Realization) : Prop where
   
  cell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ d.face → R'.cell σ = R.cell σ
   
  isCrosscut : IsCrosscut (frontier (R.cell d.face)) (R'.cellUnion d.earCells)
    (R.pos d.source) (R.pos d.target)
   
  isCutPair : IsCutPair (frontier (R.cell d.face)) (R.pos d.source) (R.pos d.target)
    (R.cellUnion d.cells₁) (R.cellUnion d.cells₂)
   
  cell_face₁ : R'.cell d.face₁ = inside (R.cellUnion d.cells₁ ∪ R'.cellUnion d.earCells)
   
  cell_face₂ : R'.cell d.face₂ = inside (R.cellUnion d.cells₂ ∪ R'.cellUnion d.earCells)
   
  cellUnion_earNewCells : R'.cellUnion d.earNewCells =
    R'.cellUnion d.earCells \ {R.pos d.source, R.pos d.target}
   
  earNonempty : ∀ ⦃σ⦄, σ ∈ d.earNewCells → (R'.cell σ).Nonempty
   
  earDisjoint : ∀ ⦃σ τ⦄, σ ∈ d.earNewCells → τ ∈ d.earNewCells → σ ≠ τ →
    Disjoint (R'.cell σ) (R'.cell τ)
   
  closure_earVertex : ∀ ⦃z⦄, z ∈ V(d.ear) → z ≠ d.source → z ≠ d.target →
    closure (R'.cell z) = R'.cell z
   
  closure_earEdge : ∀ ⦃f a b⦄, d.ear.IsLink f a b →
    closure (R'.cell f) = R'.cell f ∪ (R'.cell a ∪ R'.cell b)

namespace IsCrosscutSplit

 

theorem cellUnion_cells₁ (hc : d.IsCrosscutSplit R R') :
    R'.cellUnion d.cells₁ = R.cellUnion d.cells₁ :=
  Realization.cellUnion_congr fun _ hσ => hc.cell_eq (d.cells₁_subset hσ) (d.cells₁_ne_face hσ)

theorem cellUnion_cells₂ (hc : d.IsCrosscutSplit R R') :
    R'.cellUnion d.cells₂ = R.cellUnion d.cells₂ :=
  Realization.cellUnion_congr fun _ hσ => hc.cell_eq (d.cells₂_subset hσ) (d.cells₂_ne_face hσ)

 
theorem cell_earNew_subset (hc : d.IsCrosscutSplit R R') {σ : γ} (hσ : σ ∈ d.earNewCells) :
    R'.cell σ ⊆ R'.cellUnion d.earCells \ {R.pos d.source, R.pos d.target} := by
  rw [← hc.cellUnion_earNewCells]
  exact R'.cell_subset_cellUnion hσ

 
theorem frontier_face₁ (hc : d.IsCrosscutSplit R R') :
    frontier (R'.cell d.face₁) = R.cellUnion d.cells₁ ∪ R'.cellUnion d.earCells := by
  rw [hc.cell_face₁]
  exact hc.isCrosscut.frontier_side (fun _ hs => jordan_curve_theorem hs) hc.isCutPair

theorem frontier_face₂ (hc : d.IsCrosscutSplit R R') :
    frontier (R'.cell d.face₂) = R.cellUnion d.cells₂ ∪ R'.cellUnion d.earCells := by
  rw [hc.cell_face₂]
  exact hc.isCrosscut.frontier_side (fun _ hs => jordan_curve_theorem hs) hc.isCutPair.symm

theorem disjoint_faces (hc : d.IsCrosscutSplit R R') :
    Disjoint (R'.cell d.face₁) (R'.cell d.face₂) := by
  rw [hc.cell_face₁, hc.cell_face₂]
  exact hc.isCrosscut.disjoint_sides (fun _ hs => jordan_curve_theorem hs) hc.isCutPair

theorem disjoint_face₁_earNew (hc : d.IsCrosscutSplit R R') {σ : γ} (hσ : σ ∈ d.earNewCells) :
    Disjoint (R'.cell d.face₁) (R'.cell σ) := by
  rw [hc.cell_face₁]
  exact (hc.isCrosscut.disjoint_side_crosscut (fun _ hs => jordan_curve_theorem hs)
    hc.isCutPair).mono_right (hc.cell_earNew_subset hσ)

theorem disjoint_face₂_earNew (hc : d.IsCrosscutSplit R R') {σ : γ} (hσ : σ ∈ d.earNewCells) :
    Disjoint (R'.cell d.face₂) (R'.cell σ) := by
  rw [hc.cell_face₂]
  exact (hc.isCrosscut.disjoint_side_crosscut (fun _ hs => jordan_curve_theorem hs)
    hc.isCutPair.symm).mono_right (hc.cell_earNew_subset hσ)

 






theorem isRefinement (hc : d.IsCrosscutSplit R R') (hJ : R.IsFaceJordan) :
    d.IsRefinement R R' where
  cell_eq := hc.cell_eq
  cell_face := by
    calc R.cell d.face = inside (frontier (R.cell d.face)) := hJ.cell_eq_inside d.face_mem
      _ = inside (R.cellUnion d.cells₁ ∪ R'.cellUnion d.earCells) ∪
            inside (R.cellUnion d.cells₂ ∪ R'.cellUnion d.earCells) ∪
            (R'.cellUnion d.earCells \ {R.pos d.source, R.pos d.target}) :=
          hc.isCrosscut.inside_eq_split (fun _ hs => jordan_curve_theorem hs) hc.isCutPair
            hc.isCrosscut.hasArcCollars
      _ = R'.cell d.face₁ ∪ R'.cell d.face₂ ∪ R'.cellUnion d.earNewCells := by
          rw [hc.cell_face₁, hc.cell_face₂, hc.cellUnion_earNewCells]
  nonempty := by
    rintro σ (hσ | (rfl | rfl))
    · exact hc.earNonempty hσ
    · rw [hc.cell_face₁]
      exact hc.isCrosscut.side_nonempty (fun _ hs => jordan_curve_theorem hs) hc.isCutPair
    · rw [hc.cell_face₂]
      exact hc.isCrosscut.side_nonempty (fun _ hs => jordan_curve_theorem hs) hc.isCutPair.symm
  disjoint := by
    rintro σ τ (hσ | (rfl | rfl)) (hτ | (rfl | rfl)) hne
    · exact hc.earDisjoint hσ hτ hne
    · exact (hc.disjoint_face₁_earNew hσ).symm
    · exact (hc.disjoint_face₂_earNew hσ).symm
    · exact hc.disjoint_face₁_earNew hτ
    · exact absurd rfl hne
    · exact hc.disjoint_faces
    · exact hc.disjoint_face₂_earNew hτ
    · exact hc.disjoint_faces.symm
    · exact absurd rfl hne
  closure_earVertex := hc.closure_earVertex
  closure_earEdge := hc.closure_earEdge
  closure_face₁ := by
    rw [hc.cell_face₁, hc.cellUnion_cells₁,
      hc.isCrosscut.closure_side (fun _ hs => jordan_curve_theorem hs) hc.isCutPair]
    simp only [Set.union_assoc, Set.union_comm]
  closure_face₂ := by
    rw [hc.cell_face₂, hc.cellUnion_cells₂,
      hc.isCrosscut.closure_side (fun _ hs => jordan_curve_theorem hs) hc.isCutPair.symm]
    simp only [Set.union_assoc, Set.union_comm]

 


theorem isFaceJordan (hc : d.IsCrosscutSplit R R') (hJ : R.IsFaceJordan) : R'.IsFaceJordan where
  isJordanCurve := by
    intro F hF
    rw [splitFace_faces] at hF
    rcases hF with rfl | rfl | ⟨hFc, hFf⟩
    · rw [hc.frontier_face₁]; exact hc.isCrosscut.isJordanCurve_union hc.isCutPair
    · rw [hc.frontier_face₂]; exact hc.isCrosscut.isJordanCurve_union hc.isCutPair.symm
    · rw [hc.cell_eq (S.mem_cells_of_mem_faces hFc) hFf]; exact hJ.isJordanCurve hFc
  cell_eq_inside := by
    intro F hF
    rw [splitFace_faces] at hF
    rcases hF with rfl | rfl | ⟨hFc, hFf⟩
    · rw [hc.frontier_face₁]; exact hc.cell_face₁
    · rw [hc.frontier_face₂]; exact hc.cell_face₂
    · rw [hc.cell_eq (S.mem_cells_of_mem_faces hFc) hFf]; exact hJ.cell_eq_inside hFc

 


theorem isCellDecomposition_and_isFaceJordan (hc : d.IsCrosscutSplit R R')
    (hS : S.CombInvariants) {D : Set Plane} (h : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    R'.IsCellDecomposition D ∧ R'.IsFaceJordan ∧ R'.Refines R d.parent :=
  ⟨(hc.isRefinement hJ).isCellDecomposition hS h, hc.isFaceJordan hJ,
    (hc.isRefinement hJ).refines hS h⟩

end IsCrosscutSplit

end SplitData

end CellStructure

end Schoenflies
