/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/SquareMesh.lean.
-/
import FiniteAvalanches.Support.Schoenflies.OverlayGraph
import FiniteAvalanches.Support.Schoenflies.ModelCurve
import FiniteAvalanches.Support.Schoenflies.Graph.OuterFace
import FiniteAvalanches.Support.Schoenflies.Graph.Redrawing

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





































































open Metric Set
open scoped Graph

namespace Schoenflies

 

 

def ringSet (r : ℝ) : Set Plane := {x : Plane | Plane.supNorm x = r}

theorem ringSet_one : ringSet 1 = modelCurve := rfl

 
def ringPieces (r : ℝ) : List Piece :=
  [(Plane.mk r r, Plane.mk (-r) r),
   (Plane.mk (-r) r, Plane.mk (-r) (-r)),
   (Plane.mk (-r) (-r), Plane.mk r (-r)),
   (Plane.mk r (-r), Plane.mk r r)]

theorem segment_symm_Icc {r : ℝ} (hr : 0 ≤ r) :
    segment ℝ (-r) r = Icc (-r) r := segment_eq_Icc (by linarith)

theorem segment_symm_Icc' {r : ℝ} (hr : 0 ≤ r) :
    segment ℝ r (-r) = Icc (-r) r := by
  rw [segment_symm]; exact segment_symm_Icc hr

 
theorem cover_ringPieces {r : ℝ} (hr : 0 ≤ r) : cover (ringPieces r) = ringSet r := by
  ext x
  simp only [ringPieces, cover_cons, cover_nil, union_empty, mem_union, Piece.seg,
    mem_segment_horiz, mem_segment_vert, segment_symm_Icc hr, segment_symm_Icc' hr,
    mem_Icc, ringSet, mem_setOf_eq, Plane.supNorm]
  
  
  have hleft : ∀ u v : ℝ, |u| = r → |v| ≤ r → max |u| |v| = r := by
    intro u v hu hv; rw [hu]; exact max_eq_left hv
  have hright : ∀ u v : ℝ, |u| ≤ r → |v| = r → max |u| |v| = r := by
    intro u v hu hv; rw [hv]; exact max_eq_right hu
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact hright _ _ (abs_le.2 ⟨h2, h3⟩) (by rw [h1, abs_of_nonneg hr])
    · exact hleft _ _ (by rw [h1, abs_neg, abs_of_nonneg hr]) (abs_le.2 ⟨h2, h3⟩)
    · exact hright _ _ (abs_le.2 ⟨h2, h3⟩) (by rw [h1, abs_neg, abs_of_nonneg hr])
    · exact hleft _ _ (by rw [h1, abs_of_nonneg hr]) (abs_le.2 ⟨h2, h3⟩)
  · intro h
    have h0 : |x 0| ≤ r := h ▸ le_max_left _ _
    have h1 : |x 1| ≤ r := h ▸ le_max_right _ _
    rcases max_choice |x 0| |x 1| with hm | hm
    · rcases abs_eq hr |>.1 (hm.symm.trans h) with he | he
      · exact Or.inr (Or.inr (Or.inr ⟨he, (abs_le.1 h1).1, (abs_le.1 h1).2⟩))
      · exact Or.inr (Or.inl ⟨he, (abs_le.1 h1).1, (abs_le.1 h1).2⟩)
    · rcases abs_eq hr |>.1 (hm.symm.trans h) with he | he
      · exact Or.inl ⟨he, (abs_le.1 h0).1, (abs_le.1 h0).2⟩
      · exact Or.inr (Or.inr (Or.inl ⟨he, (abs_le.1 h0).1, (abs_le.1 h0).2⟩))

theorem mk_ne_mk_of_fst {a b c d : ℝ} (h : a ≠ c) : Plane.mk a b ≠ Plane.mk c d := fun he => by
  rw [← Plane.mk_zero a b, he, Plane.mk_zero] at h; exact h rfl

theorem mk_ne_mk_of_snd {a b c d : ℝ} (h : b ≠ d) : Plane.mk a b ≠ Plane.mk c d := fun he => by
  rw [← Plane.mk_one a b, he, Plane.mk_one] at h; exact h rfl

 
theorem ringPieces_nondeg {r : ℝ} (hr : 0 < r) : ∀ P ∈ ringPieces r, P.Nondeg := by
  have hne : (r : ℝ) ≠ -r := by intro h; linarith
  intro P hP
  simp only [ringPieces, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact mk_ne_mk_of_fst hne
  · exact mk_ne_mk_of_snd hne
  · exact mk_ne_mk_of_fst hne.symm
  · exact mk_ne_mk_of_snd hne.symm

 
theorem mem_ringSet_smul {t r : ℝ} (ht : 0 ≤ t) {x : Plane} (hx : x ∈ ringSet r) :
    t • x ∈ ringSet (t * r) := by
  change Plane.supNorm (t • x) = t * r
  rw [Plane.supNorm_smul, abs_of_nonneg ht]
  exact congrArg (fun s => t * s) hx

theorem supNorm_smul_of_mem_modelCurve {t : ℝ} (ht : 0 ≤ t) {z : Plane} (hz : z ∈ modelCurve) :
    Plane.supNorm (t • z) = t := by
  rw [Plane.supNorm_smul, abs_of_nonneg ht, show Plane.supNorm z = 1 from hz, mul_one]

theorem inv_cast_lt_one {N : ℕ} (hN : 2 ≤ N) : ((N : ℝ)⁻¹) < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hN)

theorem inv_cast_pos {N : ℕ} (hN : 2 ≤ N) : (0 : ℝ) < (N : ℝ)⁻¹ := by
  have : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  positivity

 






theorem mem_smul_segment {a b : ℝ} {z x : Plane} :
    x ∈ segment ℝ (a • z) (b • z) ↔ ∃ t ∈ segment ℝ a b, x = t • z := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨p * a + q * b, ⟨p, q, hp, hq, hpq, rfl⟩, ?_⟩
    module
  · rintro ⟨t, ⟨p, q, hp, hq, hpq, rfl⟩, rfl⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    module

 
theorem smul_segment_eq_image {a b : ℝ} (hab : a ≤ b) (z : Plane) :
    segment ℝ (a • z) (b • z) = (fun t : ℝ => t • z) '' Icc a b := by
  ext x
  rw [mem_smul_segment, segment_eq_Icc hab]
  simp only [mem_image]
  exact ⟨fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩, fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩⟩

 

 
noncomputable def spokePiece (N : ℕ) (z : Plane) : Piece := (z, ((N : ℝ)⁻¹) • z)

 
theorem spokePiece_seg {N : ℕ} (hN : 2 ≤ N) (z : Plane) :
    (spokePiece N z).seg = (fun t : ℝ => t • z) '' Icc ((N : ℝ)⁻¹) 1 := by
  have key : (spokePiece N z).seg = segment ℝ (((N : ℝ)⁻¹) • z) ((1 : ℝ) • z) := by
    rw [Piece.seg, spokePiece, one_smul, segment_symm]
  rw [key, smul_segment_eq_image (inv_cast_lt_one hN).le]

 
theorem spokePiece_inter_modelCurve {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    (spokePiece N z).seg ∩ modelCurve = {z} := by
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hx, hxS⟩
    rw [spokePiece_seg hN] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have h0 : (0 : ℝ) ≤ t := le_trans (inv_cast_pos hN).le ht.1
    have : t = 1 := by
      have hval := supNorm_smul_of_mem_modelCurve h0 hz
      rw [show Plane.supNorm (t • z) = 1 from hxS] at hval
      exact hval.symm
    simp only [this, one_smul]
  · rintro rfl
    exact ⟨left_mem_segment ℝ _ _, hz⟩

 
theorem spokePiece_subset_closedSquare {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    (spokePiece N z).seg ⊆ Plane.closedSquare 0 1 := by
  rw [spokePiece_seg hN]
  rintro _ ⟨t, ht, rfl⟩
  have h0 : (0 : ℝ) ≤ t := le_trans (inv_cast_pos hN).le ht.1
  exact mem_closedSquare_zero_one.2 (by rw [supNorm_smul_of_mem_modelCurve h0 hz]; exact ht.2)

theorem spokePiece_nondeg {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    (spokePiece N z).Nondeg := by
  intro h
  have h2 : Plane.supNorm (((N : ℝ)⁻¹) • z) = (N : ℝ)⁻¹ :=
    supNorm_smul_of_mem_modelCurve (inv_cast_pos hN).le hz
  rw [show (((N : ℝ)⁻¹) • z) = z from h.symm, show Plane.supNorm z = 1 from hz] at h2
  have := inv_cast_lt_one hN
  linarith

 













theorem cover_map {α : Type*} (f : α → Piece) (l : List α) :
    cover (l.map f) = ⋃ a ∈ l, (f a).seg := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, cover_cons, ih]; simp

theorem cover_flatMap' {α : Type*} (f : α → List Piece) (l : List α) :
    cover (l.flatMap f) = ⋃ a ∈ l, cover (f a) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, cover_append, ih]; simp

theorem mem_cover_iff {x : Plane} {l : List Piece} : x ∈ cover l ↔ ∃ P ∈ l, x ∈ P.seg := by
  simp only [cover, mem_iUnion, exists_prop]

 
theorem splitAt_end_of_mem (p : Plane) (P : Piece) (hmem : p ∈ P.seg) :
    ∃ R ∈ splitAt p P, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  classical
  by_cases hp : p ∈ P.interior
  · refine ⟨(P.1, p), by rw [splitAt, if_pos hp]; simp, ?_, Or.inr rfl⟩
    exact (convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hmem
  · refine ⟨P, by rw [splitAt, if_neg hp]; simp, subset_rfl, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hp (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hmem)

 
theorem splitAt_preserves_end (q : Plane) {p : Plane} {P : Piece} (h : p = P.1 ∨ p = P.2) :
    ∃ R ∈ splitAt q P, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  classical
  by_cases hq : q ∈ P.interior
  · have hqseg : q ∈ P.seg := openSegment_subset_segment ℝ _ _ hq
    rcases h with rfl | rfl
    · refine ⟨(P.1, q), by rw [splitAt, if_pos hq]; simp, ?_, Or.inl rfl⟩
      exact (convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hqseg
    · refine ⟨(q, P.2), by rw [splitAt, if_pos hq]; simp, ?_, Or.inr rfl⟩
      exact (convex_segment P.1 P.2).segment_subset hqseg (right_mem_segment ℝ _ _)
  · exact ⟨P, by rw [splitAt, if_neg hq]; simp, subset_rfl, h⟩

theorem splitAllAt_preserves_end (q : Plane) {p : Plane} {P : Piece} {pieces : List Piece}
    (h : ∃ R ∈ pieces, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2)) :
    ∃ R ∈ splitAllAt q pieces, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  obtain ⟨R, hR, hsub, hend⟩ := h
  obtain ⟨R', hR', hsub', hend'⟩ := splitAt_preserves_end q hend
  exact ⟨R', List.mem_flatMap.2 ⟨R, hR, hR'⟩, hsub'.trans hsub, hend'⟩

theorem subdivide_preserves_end (points : List Plane) {pieces : List Piece} {p : Plane}
    {P : Piece} (h : ∃ R ∈ pieces, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2)) :
    ∃ R ∈ subdivide pieces points, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  induction points generalizing pieces with
  | nil => exact h
  | cons q qs ih => exact ih (splitAllAt_preserves_end q h)

 

theorem subdivide_covers_source (points : List Plane) : ∀ (pieces : List Piece) (P : Piece),
    P ∈ pieces → ∀ x ∈ P.seg,
      ∃ Q ∈ subdivide pieces points, x ∈ Q.seg ∧ Q.seg ⊆ P.seg := by
  induction points with
  | nil => exact fun _ P hP x hx => ⟨P, hP, hx, subset_rfl⟩
  | cons q qs ih =>
    intro pieces P hP x hx
    obtain ⟨P', hP', hxP'⟩ :=
      mem_cover_iff.1 (show x ∈ cover (splitAt q P) by rw [splitAt_cover]; exact hx)
    obtain ⟨Q, hQ, hxQ, hsub⟩ :=
      ih (splitAllAt q pieces) P' (List.mem_flatMap.2 ⟨P, hP, hP'⟩) x hxP'
    exact ⟨Q, hQ, hxQ, hsub.trans (splitAt_subset q P P' hP').1⟩

 
theorem subdivide_end_of_mem (points : List Plane) : ∀ (pieces : List Piece) (p : Plane),
    p ∈ points → ∀ P ∈ pieces, p ∈ P.seg →
      ∃ Q ∈ subdivide pieces points, Q.seg ⊆ P.seg ∧ (p = Q.1 ∨ p = Q.2) := by
  induction points with
  | nil => intro _ p hp; simp at hp
  | cons q qs ih =>
    intro pieces p hp P hP hmem
    rcases List.mem_cons.1 hp with rfl | hp'
    · 
      obtain ⟨R, hR, hsub, hend⟩ := splitAt_end_of_mem p P hmem
      exact subdivide_preserves_end qs ⟨R, List.mem_flatMap.2 ⟨P, hP, hR⟩, hsub, hend⟩
    · obtain ⟨P', hP', hpP'⟩ :=
        mem_cover_iff.1 (show p ∈ cover (splitAt q P) by rw [splitAt_cover]; exact hmem)
      obtain ⟨Q, hQ, hsub, hend⟩ :=
        ih (splitAllAt q pieces) p hp' P' (List.mem_flatMap.2 ⟨P, hP, hP'⟩) hpP'
      exact ⟨Q, hQ, hsub.trans (splitAt_subset q P P' hP').1, hend⟩

 





theorem EndsAreCut.mono {pieces : List Piece} {points points' : List Plane}
    (h : EndsAreCut pieces points) (hsub : points ⊆ points') : EndsAreCut pieces points' :=
  fun P hP z hz => hsub (h P hP z hz)

theorem MeetsAreCut.mono {pieces : List Piece} {points points' : List Plane}
    (h : MeetsAreCut pieces points) (hsub : points ⊆ points') : MeetsAreCut pieces points' := by
  intro P hP Q hQ hPQ hne
  obtain ⟨u, v, huv, hu, hv⟩ := h P hP Q hQ hPQ hne
  exact ⟨u, v, huv, hsub hu, hsub hv⟩

 







 
noncomputable def meshRadii (N : ℕ) : List ℝ :=
  (List.range N).map fun j : ℕ => ((j : ℝ) + 1) / (N : ℝ)

theorem mem_meshRadii {N : ℕ} {r : ℝ} :
    r ∈ meshRadii N ↔ ∃ j < N, r = ((j : ℝ) + 1) / N := by
  rw [meshRadii]
  constructor
  · intro hr
    obtain ⟨j, hj, hval⟩ := List.mem_map.1 hr
    exact ⟨j, List.mem_range.1 hj, hval.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

theorem meshRadii_pos {N : ℕ} (hN : 2 ≤ N) {r : ℝ} (hr : r ∈ meshRadii N) : 0 < r := by
  obtain ⟨j, _, rfl⟩ := mem_meshRadii.1 hr
  have : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  positivity

theorem meshRadii_le_one {N : ℕ} (hN : 2 ≤ N) {r : ℝ} (hr : r ∈ meshRadii N) : r ≤ 1 := by
  obtain ⟨j, hj, rfl⟩ := mem_meshRadii.1 hr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  rw [div_le_one hN0]
  have : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  linarith

theorem one_mem_meshRadii {N : ℕ} (hN : 2 ≤ N) : (1 : ℝ) ∈ meshRadii N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  refine mem_meshRadii.2 ⟨N - 1, Nat.sub_lt (by omega) one_pos, ?_⟩
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ N := by omega
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [hcast]
  field_simp
  ring

theorem inv_mem_meshRadii {N : ℕ} (hN : 2 ≤ N) : ((N : ℝ)⁻¹) ∈ meshRadii N := by
  refine mem_meshRadii.2 ⟨0, by omega, ?_⟩
  norm_num

 
noncomputable def meshSegments (N : ℕ) (fresh : List Plane) : List Piece :=
  (meshRadii N).flatMap ringPieces ++ fresh.map (spokePiece N)

theorem mem_meshSegments {N : ℕ} {fresh : List Plane} {P : Piece} :
    P ∈ meshSegments N fresh ↔
      (∃ r ∈ meshRadii N, P ∈ ringPieces r) ∨ ∃ z ∈ fresh, P = spokePiece N z := by
  simp only [meshSegments, List.mem_append, List.mem_flatMap, List.mem_map]
  exact or_congr Iff.rfl ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩⟩

theorem cover_meshSegments {N : ℕ} (hN : 2 ≤ N) (fresh : List Plane) :
    cover (meshSegments N fresh) =
      (⋃ r ∈ meshRadii N, ringSet r) ∪ ⋃ z ∈ fresh, (spokePiece N z).seg := by
  rw [meshSegments, cover_append, cover_flatMap', cover_map]
  congr 1
  exact iUnion₂_congr fun r hr => cover_ringPieces (meshRadii_pos hN hr).le

theorem meshSegments_nondeg {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) : ∀ P ∈ meshSegments N fresh, P.Nondeg := by
  intro P hP
  rcases mem_meshSegments.1 hP with ⟨r, hr, hPr⟩ | ⟨z, hz, rfl⟩
  · exact ringPieces_nondeg (meshRadii_pos hN hr) P hPr
  · exact spokePiece_nondeg hN (hfresh z hz)

 
theorem ringPieces_seg_subset {r : ℝ} (hr : 0 ≤ r) {P : Piece} (hP : P ∈ ringPieces r) :
    P.seg ⊆ ringSet r := by
  rw [← cover_ringPieces hr]
  exact fun x hx => mem_cover_iff.2 ⟨P, hP, hx⟩

 
theorem meshSegments_subset_closedSquare {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {P : Piece} (hP : P ∈ meshSegments N fresh) :
    P.seg ⊆ Plane.closedSquare 0 1 := by
  rcases mem_meshSegments.1 hP with ⟨r, hr, hPr⟩ | ⟨z, hz, rfl⟩
  · refine (ringPieces_seg_subset (meshRadii_pos hN hr).le hPr).trans ?_
    exact fun x hx => mem_closedSquare_zero_one.2 (le_of_eq_of_le hx (meshRadii_le_one hN hr))
  · exact spokePiece_subset_closedSquare hN (hfresh z hz)

 





open scoped Classical in
 
noncomputable def meshCutPoints (N : ℕ) (fresh : List Plane) : List Plane :=
  (exists_cut_points (meshSegments N fresh)).choose

theorem meshCutPoints_spec (N : ℕ) (fresh : List Plane) :
    EndsAreCut (meshSegments N fresh) (meshCutPoints N fresh) ∧
      MeetsAreCut (meshSegments N fresh) (meshCutPoints N fresh) :=
  (exists_cut_points (meshSegments N fresh)).choose_spec

 
noncomputable def meshPoints (N : ℕ) (fresh anchors : List Plane) : List Plane :=
  anchors ++ meshCutPoints N fresh

theorem meshPoints_endsAreCut (N : ℕ) (fresh anchors : List Plane) :
    EndsAreCut (meshSegments N fresh) (meshPoints N fresh anchors) :=
  (meshCutPoints_spec N fresh).1.mono (List.subset_append_right _ _)

theorem meshPoints_meetsAreCut (N : ℕ) (fresh anchors : List Plane) :
    MeetsAreCut (meshSegments N fresh) (meshPoints N fresh anchors) :=
  (meshCutPoints_spec N fresh).2.mono (List.subset_append_right _ _)

theorem anchors_subset_meshPoints (N : ℕ) (fresh anchors : List Plane) :
    anchors ⊆ meshPoints N fresh anchors := List.subset_append_left _ _

 
noncomputable def meshGraph (N : ℕ) (fresh anchors : List Plane) : Graph Plane Piece :=
  overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)

instance meshGraph_finite (N : ℕ) (fresh anchors : List Plane) :
    Graph.Finite (meshGraph N fresh anchors) :=
  overlayGraph_finite _ _

theorem meshGraph_isDrawing {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) :
    Graph.IsDrawing (meshGraph N fresh anchors) segmentDrawing :=
  overlayGraph_isDrawing _ _ (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors)

theorem meshGraph_pointSet (N : ℕ) (fresh anchors : List Plane) :
    Graph.pointSet (meshGraph N fresh anchors) segmentDrawing = cover (meshSegments N fresh) :=
  overlayGraph_pointSet _ _

 
theorem meshGraph_edge_source {N : ℕ} {fresh anchors : List Plane} {P : Piece}
    (hP : P ∈ E(meshGraph N fresh anchors)) :
    ∃ R ∈ meshSegments N fresh, P.seg ⊆ R.seg := by
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  obtain ⟨R, hR, hsub, -⟩ := subdivide_subset _ _ Q hQ
  exact ⟨R, hR, by rwa [orientPiece_seg]⟩

theorem meshGraph_edge_nondeg {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {P : Piece}
    (hP : P ∈ E(meshGraph N fresh anchors)) : P.Nondeg :=
  overlayPieces_nondeg _ (meshSegments_nondeg hN hfresh) P hP

theorem meshGraph_mem_vertexSet {N : ℕ} {fresh anchors : List Plane} {v : Plane} :
    v ∈ V(meshGraph N fresh anchors) ↔
      ∃ P ∈ E(meshGraph N fresh anchors), v = P.1 ∨ v = P.2 := Iff.rfl

 
theorem outer_ringPieces_mem {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {R : Piece}
    (hR : R ∈ ringPieces 1) : R ∈ meshSegments N fresh :=
  mem_meshSegments.2 (Or.inl ⟨1, one_mem_meshRadii hN, hR⟩)

theorem spokePiece_mem_meshSegments {N : ℕ} {fresh : List Plane} {z : Plane} (hz : z ∈ fresh) :
    spokePiece N z ∈ meshSegments N fresh := mem_meshSegments.2 (Or.inr ⟨z, hz, rfl⟩)

 
theorem fresh_mem_meshPoints {N : ℕ} {fresh : List Plane} (anchors : List Plane) {z : Plane}
    (hz : z ∈ fresh) : z ∈ meshPoints N fresh anchors :=
  meshPoints_endsAreCut N fresh anchors _ (spokePiece_mem_meshSegments hz) z (Or.inl rfl)

 

 


theorem anchor_mem_vertexSet {N : ℕ} (hN : 2 ≤ N) {fresh anchors : List Plane} {p : Plane}
    (hp : p ∈ anchors) (hpS : p ∈ modelCurve) : p ∈ V(meshGraph N fresh anchors) := by
  obtain ⟨R, hR, hpR⟩ :=
    mem_cover_iff.1 (show p ∈ cover (ringPieces 1) by rw [cover_ringPieces zero_le_one]; exact hpS)
  obtain ⟨Q, hQ, -, hend⟩ := subdivide_end_of_mem (meshPoints N fresh anchors)
    (meshSegments N fresh) p (anchors_subset_meshPoints N fresh anchors hp) R
    (outer_ringPieces_mem hN hR) hpR
  exact ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, (orientPiece_ends Q p).2 hend⟩

 





 
def outerEdges (N : ℕ) (fresh anchors : List Plane) : Set Piece :=
  {P | P ∈ E(meshGraph N fresh anchors) ∧ P.seg ⊆ modelCurve}

 
theorem cover_outerEdges {N : ℕ} (hN : 2 ≤ N) (fresh anchors : List Plane) :
    ⋃ P ∈ outerEdges N fresh anchors, P.seg = modelCurve := by
  refine subset_antisymm (iUnion₂_subset fun P hP => hP.2) fun x hx => ?_
  obtain ⟨R, hR, hxR⟩ :=
    mem_cover_iff.1 (show x ∈ cover (ringPieces 1) by rw [cover_ringPieces zero_le_one]; exact hx)
  obtain ⟨Q, hQ, hxQ, hsub⟩ := subdivide_covers_source (meshPoints N fresh anchors)
    (meshSegments N fresh) R (outer_ringPieces_mem hN hR) x hxR
  refine mem_iUnion₂.2 ⟨orientPiece Q, ⟨mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, ?_⟩, ?_⟩
  · rw [orientPiece_seg]
    exact hsub.trans (ringPieces_seg_subset zero_le_one hR)
  · rwa [orientPiece_seg]

 




theorem ringSet_disjoint_modelCurve {r : ℝ} (hr : r ≠ 1) : ringSet r ∩ modelCurve = ∅ := by
  ext x
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hxr hx1
  exact hr (hxr.symm.trans hx1)

theorem smul_left_inj {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) {z : Plane} (hz : z ∈ modelCurve)
    (h : t • z = s • z) : t = s := by
  rw [← supNorm_smul_of_mem_modelCurve ht hz, ← supNorm_smul_of_mem_modelCurve hs hz, h]

 

theorem meshGraph_inner_edge_at_fresh {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {P : Piece}
    (hP : P ∈ E(meshGraph N fresh anchors)) (hmeet : (P.seg ∩ modelCurve).Nonempty)
    (hnot : ¬ P.seg ⊆ modelCurve) :
    ∃ z ∈ fresh, P.seg ∩ modelCurve = {z} ∧ (z = P.1 ∨ z = P.2) ∧
      P.seg ⊆ (spokePiece N z).seg := by
  obtain ⟨R, hR, hsub⟩ := meshGraph_edge_source hP
  rcases mem_meshSegments.1 hR with ⟨r, hr, hRr⟩ | ⟨z, hz, rfl⟩
  · exfalso
    have hseg : P.seg ⊆ ringSet r :=
      hsub.trans (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr)
    by_cases h1 : r = 1
    · exact hnot (by rw [← ringSet_one, ← h1]; exact hseg)
    · obtain ⟨x, hxP, hxS⟩ := hmeet
      have hmem : x ∈ ringSet r ∩ modelCurve := ⟨hseg hxP, hxS⟩
      rw [ringSet_disjoint_modelCurve h1] at hmem
      exact hmem
  · have hle : P.seg ∩ modelCurve ⊆ {z} := by
      rw [← spokePiece_inter_modelCurve hN (hfresh z hz)]
      exact inter_subset_inter_left _ hsub
    obtain ⟨x, hxP, hxS⟩ := hmeet
    have hxz : x = z := hle ⟨hxP, hxS⟩
    subst hxz
    refine ⟨x, hz, subset_antisymm hle (singleton_subset_iff.2 ⟨hxP, hxS⟩), ?_, hsub⟩
    
    by_contra hcon
    push Not at hcon
    exact overlayPieces_avoids (meshSegments_nondeg hN hfresh) x
      (fresh_mem_meshPoints anchors hz) P hP
      (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

theorem mem_smul_openSegment {a b : ℝ} {z x : Plane} :
    x ∈ openSegment ℝ (a • z) (b • z) ↔ ∃ t ∈ openSegment ℝ a b, x = t • z := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨p * a + q * b, ⟨p, q, hp, hq, hpq, rfl⟩, ?_⟩
    module
  · rintro ⟨t, ⟨p, q, hp, hq, hpq, rfl⟩, rfl⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    module

theorem smul_openSegment_eq_image {a b : ℝ} (hab : a < b) (z : Plane) :
    openSegment ℝ (a • z) (b • z) = (fun t : ℝ => t • z) '' Ioo a b := by
  ext x
  rw [mem_smul_openSegment, openSegment_eq_Ioo hab]
  simp only [mem_image]
  exact ⟨fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩, fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩⟩

 


theorem spoke_subpiece_interior {N : ℕ} (hN : 2 ≤ N) {z : Plane}
    {P : Piece} (hnd : P.Nondeg) (hsub : P.seg ⊆ (spokePiece N z).seg)
    (hend : z = P.1 ∨ z = P.2) :
    ∃ t₀ : ℝ, t₀ < 1 ∧ P.interior = (fun t : ℝ => t • z) '' Ioo t₀ 1 := by
  have key : ∀ q : Plane, q ∈ (spokePiece N z).seg → q ≠ z →
      ∃ t₀ : ℝ, t₀ < 1 ∧ openSegment ℝ z q = (fun t : ℝ => t • z) '' Ioo t₀ 1 := by
    intro q hq hne
    rw [spokePiece_seg hN] at hq
    obtain ⟨t₀, ht₀, rfl⟩ := hq
    have hlt : t₀ < 1 := lt_of_le_of_ne ht₀.2 fun h => hne (by simp [h])
    refine ⟨t₀, hlt, ?_⟩
    have hz1 : openSegment ℝ z (t₀ • z) = openSegment ℝ (t₀ • z) ((1 : ℝ) • z) := by
      rw [one_smul, openSegment_symm]
    rw [hz1, smul_openSegment_eq_image hlt]
  rcases hend with h | h
  · obtain ⟨t₀, hlt, heq⟩ :=
      key P.2 (hsub (right_mem_segment ℝ _ _)) (by rw [h]; exact Ne.symm hnd)
    exact ⟨t₀, hlt, by change openSegment ℝ P.1 P.2 = _; rw [← h, heq]⟩
  · obtain ⟨t₀, hlt, heq⟩ := key P.1 (hsub (left_mem_segment ℝ _ _)) (by rw [h]; exact hnd)
    exact ⟨t₀, hlt, by change openSegment ℝ P.1 P.2 = _; rw [openSegment_symm, ← h, heq]⟩

 
theorem exists_inner_edge_at_fresh {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ w ∈ fresh, w ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    ∃ P ∈ E(meshGraph N fresh anchors),
      (z = P.1 ∨ z = P.2) ∧ ¬ P.seg ⊆ modelCurve ∧ P.seg ⊆ (spokePiece N z).seg := by
  obtain ⟨Q, hQ, hsub, hend⟩ := subdivide_end_of_mem (meshPoints N fresh anchors)
    (meshSegments N fresh) z (fresh_mem_meshPoints anchors hz) (spokePiece N z)
    (spokePiece_mem_meshSegments hz) (left_mem_segment ℝ _ _)
  have hnd : Q.Nondeg :=
    subdivide_ne (meshPoints N fresh anchors) (meshSegments_nondeg hN hfresh) Q hQ
  refine ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, (orientPiece_ends Q z).2 hend, ?_, ?_⟩
  · rw [orientPiece_seg]
    intro hcon
    
    have hsing : Q.seg ⊆ {z} := by
      rw [← spokePiece_inter_modelCurve hN (hfresh z hz)]
      exact subset_inter hsub hcon
    exact hnd ((hsing (left_mem_segment ℝ _ _)).trans (hsing (right_mem_segment ℝ _ _)).symm)
  · rw [orientPiece_seg]; exact hsub

 
theorem inner_edge_at_fresh_unique {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {z : Plane} (hz : z ∈ fresh)
    {P Q : Piece} (hP : P ∈ E(meshGraph N fresh anchors)) (hendP : z = P.1 ∨ z = P.2)
    (hnotP : ¬ P.seg ⊆ modelCurve) (hQ : Q ∈ E(meshGraph N fresh anchors))
    (hendQ : z = Q.1 ∨ z = Q.2) (hnotQ : ¬ Q.seg ⊆ modelCurve) : P = Q := by
  have hzS : z ∈ modelCurve := hfresh z hz
  
  have spoke_of : ∀ R : Piece, R ∈ E(meshGraph N fresh anchors) → (z = R.1 ∨ z = R.2) →
      ¬ R.seg ⊆ modelCurve → R.seg ⊆ (spokePiece N z).seg := by
    intro R hR hendR hnotR
    have hzR : z ∈ R.seg := by
      rcases hendR with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    obtain ⟨w, hw, hmeetw, -, hsubw⟩ :=
      meshGraph_inner_edge_at_fresh hN hfresh hR ⟨z, hzR, hzS⟩ hnotR
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hmeetw ▸ (show z ∈ R.seg ∩ modelCurve from ⟨hzR, hzS⟩)
      exact this
    rwa [← hzw] at hsubw
  obtain ⟨tP, hltP, hintP⟩ := spoke_subpiece_interior hN
    (meshGraph_edge_nondeg hN hfresh hP) (spoke_of P hP hendP hnotP) hendP
  obtain ⟨tQ, hltQ, hintQ⟩ := spoke_subpiece_interior hN
    (meshGraph_edge_nondeg hN hfresh hQ) (spoke_of Q hQ hendQ hnotQ) hendQ
  by_contra hne
  
  set s : ℝ := (max tP tQ + 1) / 2 with hs
  have hs1 : s < 1 := by
    rw [hs]
    rcases max_cases tP tQ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  have hsP : tP < s := by
    rw [hs]; have : tP ≤ max tP tQ := le_max_left _ _
    have : max tP tQ < 1 := max_lt hltP hltQ
    linarith [le_max_left tP tQ]
  have hsQ : tQ < s := by
    rw [hs]; have : max tP tQ < 1 := max_lt hltP hltQ
    linarith [le_max_right tP tQ]
  refine overlayPieces_disjoint_interiors (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors) hP hQ hne
    (x := s • z) ?_ ?_
  · rw [hintP]; exact ⟨s, ⟨hsP, hs1⟩, rfl⟩
  · rw [hintQ]; exact ⟨s, ⟨hsQ, hs1⟩, rfl⟩

 
theorem unique_inner_edge_at_fresh {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    ∃! P : Piece, P ∈ E(meshGraph N fresh anchors) ∧ (z = P.1 ∨ z = P.2) ∧
      ¬ P.seg ⊆ modelCurve := by
  obtain ⟨P, hP, hend, hnot, -⟩ := exists_inner_edge_at_fresh hN hfresh anchors hz
  exact ⟨P, ⟨hP, hend, hnot⟩, fun Q hQ =>
    inner_edge_at_fresh_unique hN hfresh hz hQ.1 hQ.2.1 hQ.2.2 hP hend hnot⟩

 













theorem continuous_supNorm : Continuous Plane.supNorm :=
  (continuous_abs.comp (Plane.continuous_coord 0)).max
    (continuous_abs.comp (Plane.continuous_coord 1))

theorem supNorm_sub_le (x y : Plane) :
    Plane.supNorm (x - y) ≤ Plane.supNorm x + Plane.supNorm y := by
  have h := Plane.supDist_triangle x 0 y
  rw [Plane.supDist_zero, Plane.supDist_comm 0 y, Plane.supDist_zero] at h
  exact h

theorem dist_le_sqrt_two_mul_supNorm (x y : Plane) :
    dist x y ≤ Real.sqrt 2 * Plane.supNorm (x - y) := by
  rw [dist_eq_norm]; exact Plane.norm_le_sqrt_two_mul_supNorm _

 






def FreshDense (fresh : List Plane) (δ : ℝ) : Prop :=
  ∀ A : Set Plane, A ⊆ modelCurve \ {x | x ∈ fresh} → IsPreconnected A →
    ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ δ / 2

theorem ringSet_subset_cover {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {r : ℝ}
    (hr : r ∈ meshRadii N) : ringSet r ⊆ cover (meshSegments N fresh) := by
  rw [cover_meshSegments hN]
  exact fun x hx => mem_union_left _ (mem_iUnion₂.2 ⟨r, hr, hx⟩)

theorem spokePiece_seg_subset_cover {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {z : Plane}
    (hz : z ∈ fresh) : (spokePiece N z).seg ⊆ cover (meshSegments N fresh) := by
  rw [cover_meshSegments hN]
  exact fun x hx => mem_union_right _ (mem_iUnion₂.2 ⟨z, hz, hx⟩)

 

theorem radial_diam_bound {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {δ : ℝ}
    (hNδ : 2 * Real.sqrt 2 ≤ δ * N) (hdense : FreshDense fresh δ)
    {F : Set Plane} (hconn : IsPreconnected F)
    (hdisj : ∀ x ∈ F, x ∉ cover (meshSegments N fresh))
    {base : Plane} (hb : base ∈ F) (hbase : Plane.supNorm base < 1) :
    (∀ x ∈ F, Plane.supNorm x < 1) ∧
      ∀ x ∈ F, ∀ y ∈ F, dist x y ≤ δ / 2 + Real.sqrt 2 / N := by
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  
  have hring : ∀ r ∈ meshRadii N, ∀ x ∈ F, Plane.supNorm x ≠ r := fun r hr x hx he =>
    hdisj x hx (ringSet_subset_cover hN hr he)
  have himg : IsPreconnected (Plane.supNorm '' F) :=
    hconn.image _ continuous_supNorm.continuousOn
  
  set c : ℝ := Plane.supNorm base with hc
  have hc0 : 0 ≤ c := Plane.supNorm_nonneg _
  have hcN : 0 ≤ c * (N : ℝ) := mul_nonneg hc0 hNR0.le
  set k : ℕ := ⌊c * (N : ℝ)⌋₊ with hk
  have hkle : (k : ℝ) ≤ c * N := Nat.floor_le hcN
  have hklt : c * (N : ℝ) < k + 1 := Nat.lt_floor_add_one _
  have hkN : k < N := by
    rw [hk, Nat.floor_lt hcN]
    calc c * (N : ℝ) < 1 * N := by exact mul_lt_mul_of_pos_right hbase hNR0
      _ = N := one_mul _
  set a : ℝ := (k : ℝ) / N with ha
  set b : ℝ := ((k : ℝ) + 1) / N with hbdef
  have hac : a ≤ c := by rw [ha, div_le_iff₀ hNR0]; exact hkle
  have hcb : c < b := by rw [hbdef, lt_div_iff₀ hNR0]; exact hklt
  have hbmem : b ∈ meshRadii N := mem_meshRadii.2 ⟨k, hkN, rfl⟩
  have hb1 : b ≤ 1 := meshRadii_le_one hN hbmem
  have hba : b - a = 1 / (N : ℝ) := by rw [ha, hbdef, div_sub_div_same]; ring_nf
  
  have hup : ∀ x ∈ F, Plane.supNorm x < b := by
    intro x hx
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hyb⟩ :=
      himg.Icc_subset ⟨base, hb, rfl⟩ ⟨x, hx, rfl⟩ (mem_Icc.2 ⟨hcb.le, hcon⟩)
    exact hring b hbmem y hy hyb
  have hlow : ∀ x ∈ F, a ≤ Plane.supNorm x := by
    intro x hx
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · rw [ha, hk0]; simpa using Plane.supNorm_nonneg x
    · have hamem : a ∈ meshRadii N := by
        refine mem_meshRadii.2 ⟨k - 1, by omega, ?_⟩
        rw [ha]
        congr 1
        rw [Nat.cast_sub hk1, Nat.cast_one]
        ring
      have hac' : a < c := lt_of_le_of_ne hac fun he => hring a hamem base hb he.symm
      by_contra hcon
      push Not at hcon
      obtain ⟨y, hy, hya⟩ :=
        himg.Icc_subset ⟨x, hx, rfl⟩ ⟨base, hb, rfl⟩ (mem_Icc.2 ⟨hcon.le, hac'.le⟩)
      exact hring a hamem y hy hya
  refine ⟨fun x hx => lt_of_lt_of_le (hup x hx) hb1, ?_⟩
  
  have hthin : Real.sqrt 2 / (N : ℝ) ≤ δ / 2 := by
    rw [div_le_div_iff₀ hNR0 two_pos]
    linarith
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · 
    have hsmall : ∀ x ∈ F, Plane.supNorm x < 1 / (N : ℝ) := by
      intro x hx
      have := hup x hx
      rwa [hbdef, hk0, Nat.cast_zero, zero_add] at this
    intro x hx y hy
    calc dist x y ≤ Real.sqrt 2 * Plane.supNorm (x - y) := dist_le_sqrt_two_mul_supNorm x y
      _ ≤ Real.sqrt 2 * (Plane.supNorm x + Plane.supNorm y) :=
          mul_le_mul_of_nonneg_left (supNorm_sub_le x y) hsqrt.le
      _ ≤ Real.sqrt 2 * (1 / (N : ℝ) + 1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add (hsmall x hx).le (hsmall y hy).le) hsqrt.le
      _ = Real.sqrt 2 / N + Real.sqrt 2 / N := by ring
      _ ≤ δ / 2 + Real.sqrt 2 / N := by linarith
  · 
    have hainv : (N : ℝ)⁻¹ ≤ a := by
      rw [ha, inv_eq_one_div, div_le_div_iff_of_pos_right hNR0]
      exact_mod_cast hk1
    have hapos : 0 < a := lt_of_lt_of_le (by positivity) hainv
    have hpos : ∀ x ∈ F, 0 < Plane.supNorm x := fun x hx => lt_of_lt_of_le hapos (hlow x hx)
    set g : Plane → Plane := fun x => (Plane.supNorm x)⁻¹ • x with hg
    have hrecov : ∀ x ∈ F, Plane.supNorm x • g x = x := by
      intro x hx
      rw [hg]
      simp only [smul_smul]
      rw [mul_inv_cancel₀ (ne_of_gt (hpos x hx)), one_smul]
    have hgS : ∀ x ∈ F, g x ∈ modelCurve := by
      intro x hx
      change Plane.supNorm ((Plane.supNorm x)⁻¹ • x) = 1
      rw [Plane.supNorm_smul, abs_of_nonneg (inv_nonneg.2 (Plane.supNorm_nonneg x))]
      exact inv_mul_cancel₀ (ne_of_gt (hpos x hx))
    have hgcont : ContinuousOn g F :=
      ContinuousOn.smul (continuous_supNorm.continuousOn.inv₀ fun x hx => ne_of_gt (hpos x hx))
        continuousOn_id
    have hgavoid : ∀ x ∈ F, g x ∈ modelCurve \ {w : Plane | w ∈ fresh} := by
      intro x hx
      refine ⟨hgS x hx, fun hmem => hdisj x hx ?_⟩
      
      refine spokePiece_seg_subset_cover hN hmem ?_
      rw [spokePiece_seg hN]
      exact ⟨Plane.supNorm x, ⟨le_trans hainv (hlow x hx),
        le_trans (hup x hx).le hb1⟩, hrecov x hx⟩
    have hgdist : ∀ x ∈ F, ∀ y ∈ F, dist (g x) (g y) ≤ δ / 2 := fun x hx y hy =>
      hdense (g '' F) (by rintro _ ⟨w, hw, rfl⟩; exact hgavoid w hw) (hconn.image g hgcont)
        (g x) ⟨x, hx, rfl⟩ (g y) ⟨y, hy, rfl⟩
    intro x hx y hy
    have hsplit : x - y = Plane.supNorm x • (g x - g y)
        + (Plane.supNorm x - Plane.supNorm y) • g y := by
      rw [smul_sub, sub_smul, hrecov x hx, hrecov y hy]
      abel
    have hnormy : ‖g y‖ ≤ Real.sqrt 2 := by
      have := Plane.norm_le_sqrt_two_mul_supNorm (g y)
      rwa [show Plane.supNorm (g y) = 1 from hgS y hy, mul_one] at this
    have hts : |Plane.supNorm x - Plane.supNorm y| ≤ 1 / (N : ℝ) := by
      rw [← hba]
      exact abs_le.2 ⟨by linarith [hlow x hx, hup y hy], by linarith [hup x hx, hlow y hy]⟩
    have hx1 : Plane.supNorm x ≤ 1 := le_of_lt (lt_of_lt_of_le (hup x hx) hb1)
    calc dist x y = ‖Plane.supNorm x • (g x - g y)
          + (Plane.supNorm x - Plane.supNorm y) • g y‖ := by rw [dist_eq_norm, hsplit]
      _ ≤ ‖Plane.supNorm x • (g x - g y)‖
          + ‖(Plane.supNorm x - Plane.supNorm y) • g y‖ := norm_add_le _ _
      _ = Plane.supNorm x * ‖g x - g y‖
          + |Plane.supNorm x - Plane.supNorm y| * ‖g y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (Plane.supNorm_nonneg x)]
      _ ≤ 1 * (δ / 2) + 1 / (N : ℝ) * Real.sqrt 2 := by
          refine add_le_add (mul_le_mul hx1 ?_ (norm_nonneg _) zero_le_one)
            (mul_le_mul hts hnormy (norm_nonneg _) (by positivity))
          rw [← dist_eq_norm]
          exact hgdist x hx y hy
      _ = δ / 2 + Real.sqrt 2 / N := by ring

 
theorem cover_meshSegments_subset {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) :
    cover (meshSegments N fresh) ⊆ Plane.closedSquare 0 1 := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := mem_cover_iff.1 hx
  exact meshSegments_subset_closedSquare hN hfresh hP hxP

 

theorem meshGraph_face_small {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {δ : ℝ} (hδ : 0 < δ)
    (hNδ : 2 * Real.sqrt 2 < δ * N) (hdense : FreshDense fresh δ) {base : Plane}
    (hbase : base ∈ Graph.exterior (meshGraph N fresh anchors) segmentDrawing)
    (hbdd : Bornology.IsBounded (Graph.face (meshGraph N fresh anchors) segmentDrawing base)) :
    Graph.face (meshGraph N fresh anchors) segmentDrawing base ⊆ Plane.openSquare 0 1 ∧
      Metric.diam (Graph.face (meshGraph N fresh anchors) segmentDrawing base) < δ := by
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  set F := Graph.face (meshGraph N fresh anchors) segmentDrawing base with hF
  have hpt : Graph.pointSet (meshGraph N fresh anchors) segmentDrawing
      = cover (meshSegments N fresh) := meshGraph_pointSet N fresh anchors
  have hsq : Graph.pointSet (meshGraph N fresh anchors) segmentDrawing
      ⊆ Plane.closedSquare 0 1 := by rw [hpt]; exact cover_meshSegments_subset hN hfresh
  
  have hbM : base ∉ cover (meshSegments N fresh) := by rw [← hpt]; exact hbase
  have hb1 : Plane.supNorm base < 1 := by
    rcases lt_trichotomy (Plane.supNorm base) 1 with h | h | h
    · exact h
    · exact absurd (ringSet_subset_cover hN (one_mem_meshRadii hN) h) hbM
    · exfalso
      have hmem : base ∈ Plane.beyondSquare 1 := by
        rw [Plane.beyondSquare_eq_compl]
        exact fun hc => absurd (mem_closedSquare_zero_one.1 hc) (not_le.2 h)
      exact Graph.not_isBounded_beyondSquare 1
        (hbdd.subset (Graph.beyondSquare_subset_face hsq hmem))
  have hdisj : ∀ x ∈ F, x ∉ cover (meshSegments N fresh) := by
    intro x hx
    have := Graph.face_subset_exterior _ _ _ hx
    rwa [Graph.exterior, hpt, mem_compl_iff] at this
  obtain ⟨hin, hdist⟩ := radial_diam_bound hN hNδ.le hdense
    (Graph.isConnected_face hbase).isPreconnected hdisj (Graph.mem_face hbase) hb1
  refine ⟨fun x hx => mem_openSquare_zero_one.2 (hin x hx), ?_⟩
  have hthin : Real.sqrt 2 / (N : ℝ) < δ / 2 := by
    rw [div_lt_div_iff₀ hNR0 two_pos]; linarith
  refine lt_of_le_of_lt (Metric.diam_le_of_forall_dist_le (by positivity) hdist) ?_
  linarith

 






 
noncomputable def halfSpoke (N : ℕ) (z : Plane) : Set Plane :=
  (fun t : ℝ => t • z) '' Ico ((N : ℝ)⁻¹) 1

theorem isConnected_halfSpoke {N : ℕ} (hN : 2 ≤ N) (z : Plane) :
    IsConnected (halfSpoke N z) :=
  (isConnected_Ico (inv_cast_lt_one hN)).image _
    (Continuous.continuousOn (continuous_id.smul continuous_const))

theorem halfSpoke_subset {N : ℕ} (hN : 2 ≤ N) (z : Plane) :
    halfSpoke N z ⊆ (spokePiece N z).seg := by
  rw [halfSpoke, spokePiece_seg hN]
  exact Set.image_mono Ico_subset_Icc_self

theorem halfSpoke_disjoint_modelCurve {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    ∀ x ∈ halfSpoke N z, x ∉ modelCurve := by
  rintro _ ⟨t, ht, rfl⟩ hmem
  have h0 : (0 : ℝ) ≤ t := le_trans (inv_cast_pos hN).le ht.1
  have : t = 1 := by
    have hval := supNorm_smul_of_mem_modelCurve h0 hz
    rw [show Plane.supNorm (t • z) = 1 from hmem] at hval
    exact hval.symm
  exact absurd this (ne_of_lt ht.2)

theorem smul_mem_halfSpoke {N : ℕ} {t : ℝ} (ht : (N : ℝ)⁻¹ ≤ t) (ht1 : t < 1) (z : Plane) :
    t • z ∈ halfSpoke N z := ⟨t, ⟨ht, ht1⟩, rfl⟩

 
theorem isConnected_ringSet {r : ℝ} (hr : 0 ≤ r) : IsConnected (ringSet r) := by
  have hseg : ∀ u v : Plane, IsConnected (segment ℝ u v) := fun u v =>
    (convex_segment u v).isConnected ⟨u, left_mem_segment ℝ _ _⟩
  rw [← cover_ringPieces hr]
  simp only [ringPieces, cover_cons, cover_nil, union_empty]
  have hCD : IsConnected (segment ℝ (Plane.mk (-r) (-r)) (Plane.mk r (-r))
      ∪ segment ℝ (Plane.mk r (-r)) (Plane.mk r r)) :=
    (hseg _ _).union ⟨Plane.mk r (-r), right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩ (hseg _ _)
  have hBCD := (hseg (Plane.mk (-r) r) (Plane.mk (-r) (-r))).union
    ⟨Plane.mk (-r) (-r), right_mem_segment ℝ _ _, Or.inl (left_mem_segment ℝ _ _)⟩ hCD
  exact (hseg (Plane.mk r r) (Plane.mk (-r) r)).union
    ⟨Plane.mk (-r) r, right_mem_segment ℝ _ _, Or.inl (left_mem_segment ℝ _ _)⟩ hBCD

 
theorem isConnected_cover_diff_modelCurve {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {z₀ : Plane} (hz₀ : z₀ ∈ fresh) :
    IsConnected (cover (meshSegments N fresh) \ modelCurve) := by
  have hinvpos := inv_cast_pos hN
  have hinvlt := inv_cast_lt_one hN
  set p : Plane := ((N : ℝ)⁻¹) • z₀ with hp
  have hpring : p ∈ ringSet ((N : ℝ)⁻¹) :=
    supNorm_smul_of_mem_modelCurve hinvpos.le (hfresh z₀ hz₀)
  have hphalf : p ∈ halfSpoke N z₀ := smul_mem_halfSpoke le_rfl hinvlt z₀
  have hinvmem : ((N : ℝ)⁻¹) ∈ meshRadii N := inv_mem_meshRadii hN
  
  have hringsub : ∀ r ∈ meshRadii N, r ≠ 1 →
      ringSet r ⊆ cover (meshSegments N fresh) \ modelCurve := by
    intro r hr hr1 x hx
    exact ⟨ringSet_subset_cover hN hr hx, fun hc => hr1 (hx.symm.trans hc)⟩
  have hhalfsub : ∀ z ∈ fresh, halfSpoke N z ⊆ cover (meshSegments N fresh) \ modelCurve := by
    intro z hz x hx
    exact ⟨spokePiece_seg_subset_cover hN hz (halfSpoke_subset hN z hx),
      halfSpoke_disjoint_modelCurve hN (hfresh z hz) x hx⟩
  refine ⟨⟨p, hhalfsub z₀ hz₀ hphalf⟩, isPreconnected_of_forall p ?_⟩
  intro y hy
  obtain ⟨hyM, hyS⟩ := hy
  rw [cover_meshSegments hN] at hyM
  rcases hyM with hyr | hyz
  · 
    obtain ⟨r, hr, hyr⟩ := mem_iUnion₂.1 hyr
    have hr1 : r ≠ 1 := fun h => hyS (by rw [← ringSet_one, ← h]; exact hyr)
    have hrpos : 0 < r := meshRadii_pos hN hr
    have hrlt : r < 1 := lt_of_le_of_ne (meshRadii_le_one hN hr) hr1
    have hrinv : ((N : ℝ)⁻¹) ≤ r := by
      obtain ⟨j, hj, rfl⟩ := mem_meshRadii.1 hr
      have hNR0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
      rw [inv_eq_one_div, div_le_div_iff_of_pos_right hNR0]
      linarith [Nat.cast_nonneg (α := ℝ) j]
    refine ⟨ringSet r ∪ halfSpoke N z₀, union_subset (hringsub r hr hr1) (hhalfsub z₀ hz₀),
      Or.inr hphalf, Or.inl hyr, ?_⟩
    exact ((isConnected_ringSet hrpos.le).union
      ⟨r • z₀, supNorm_smul_of_mem_modelCurve hrpos.le (hfresh z₀ hz₀),
        smul_mem_halfSpoke hrinv hrlt z₀⟩ (isConnected_halfSpoke hN z₀)).isPreconnected
  · 
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 hyz
    rw [spokePiece_seg hN] at hyz
    obtain ⟨t, ht, rfl⟩ := hyz
    have h0 : (0 : ℝ) ≤ t := le_trans hinvpos.le ht.1
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 fun h => hyS (by
      rw [← ringSet_one]
      exact (supNorm_smul_of_mem_modelCurve h0 (hfresh z hz)).trans h)
    refine ⟨halfSpoke N z ∪ ringSet ((N : ℝ)⁻¹),
      union_subset (hhalfsub z hz) (hringsub _ hinvmem (ne_of_lt hinvlt)),
      Or.inr hpring, Or.inl (smul_mem_halfSpoke ht.1 ht1 z), ?_⟩
    exact ((isConnected_halfSpoke hN z).union
      ⟨((N : ℝ)⁻¹) • z, smul_mem_halfSpoke le_rfl hinvlt z,
        supNorm_smul_of_mem_modelCurve hinvpos.le (hfresh z hz)⟩
      (isConnected_ringSet hinvpos.le)).isPreconnected

 




 
noncomputable def meshCount (δ : ℝ) : ℕ := max 2 (⌈2 * Real.sqrt 2 / δ⌉₊ + 1)

theorem two_le_meshCount (δ : ℝ) : 2 ≤ meshCount δ := le_max_left _ _

theorem meshCount_spec {δ : ℝ} (hδ : 0 < δ) : 2 * Real.sqrt 2 < δ * meshCount δ := by
  have h1 : 2 * Real.sqrt 2 / δ < (meshCount δ : ℝ) := by
    calc 2 * Real.sqrt 2 / δ ≤ (⌈2 * Real.sqrt 2 / δ⌉₊ : ℝ) := Nat.le_ceil _
      _ < (⌈2 * Real.sqrt 2 / δ⌉₊ : ℝ) + 1 := by linarith
      _ ≤ (meshCount δ : ℝ) := by exact_mod_cast le_max_right 2 (⌈2 * Real.sqrt 2 / δ⌉₊ + 1)
  rw [div_lt_iff₀ hδ] at h1
  linarith

 


noncomputable def squareMesh (δ : ℝ) (fresh anchors : List Plane) : Graph Plane Piece :=
  meshGraph (meshCount δ) fresh anchors

instance squareMesh_finite (δ : ℝ) (fresh anchors : List Plane) :
    Graph.Finite (squareMesh δ fresh anchors) := meshGraph_finite _ _ _

 
theorem squareMesh_isDrawing {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane) :
    Graph.IsDrawing (squareMesh δ fresh anchors) segmentDrawing :=
  meshGraph_isDrawing (two_le_meshCount δ) hfresh anchors

theorem squareMesh_pointSet (δ : ℝ) (fresh anchors : List Plane) :
    Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing
      = cover (meshSegments (meshCount δ) fresh) :=
  meshGraph_pointSet _ _ _

 
theorem modelCurve_subset_squareMesh_pointSet (δ : ℝ) (fresh anchors : List Plane) :
    modelCurve ⊆ Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing := by
  rw [squareMesh_pointSet, ← ringSet_one]
  exact ringSet_subset_cover (two_le_meshCount δ) (one_mem_meshRadii (two_le_meshCount δ))

 
theorem squareMesh_pointSet_subset {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane) :
    Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing ⊆ Plane.closedSquare 0 1 := by
  rw [squareMesh_pointSet]
  exact cover_meshSegments_subset (two_le_meshCount δ) hfresh

 
theorem squareMesh_face_small {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {δ : ℝ} (hδ : 0 < δ) (hdense : FreshDense fresh δ) {anchors : List Plane} {base : Plane}
    (hbase : base ∈ Graph.exterior (squareMesh δ fresh anchors) segmentDrawing)
    (hbdd : Bornology.IsBounded (Graph.face (squareMesh δ fresh anchors) segmentDrawing base)) :
    Graph.face (squareMesh δ fresh anchors) segmentDrawing base ⊆ Plane.openSquare 0 1 ∧
      Metric.diam (Graph.face (squareMesh δ fresh anchors) segmentDrawing base) < δ :=
  meshGraph_face_small (two_le_meshCount δ) hfresh hδ (meshCount_spec hδ) hdense hbase hbdd

 
theorem squareMesh_anchor_mem_vertexSet (δ : ℝ) {fresh anchors : List Plane} {p : Plane}
    (hp : p ∈ anchors) (hpS : p ∈ modelCurve) : p ∈ V(squareMesh δ fresh anchors) :=
  anchor_mem_vertexSet (two_le_meshCount δ) hp hpS

 
theorem squareMesh_cover_outerEdges (δ : ℝ) (fresh anchors : List Plane) :
    ⋃ P ∈ outerEdges (meshCount δ) fresh anchors, P.seg = modelCurve :=
  cover_outerEdges (two_le_meshCount δ) fresh anchors

 

theorem squareMesh_inner_edge_at_fresh {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) {anchors : List Plane} {P : Piece}
    (hP : P ∈ E(squareMesh δ fresh anchors)) (hmeet : (P.seg ∩ modelCurve).Nonempty)
    (hnot : ¬ P.seg ⊆ modelCurve) :
    ∃ z ∈ fresh, P.seg ∩ modelCurve = {z} ∧ (z = P.1 ∨ z = P.2) ∧
      P.seg ⊆ (spokePiece (meshCount δ) z).seg :=
  meshGraph_inner_edge_at_fresh (two_le_meshCount δ) hfresh hP hmeet hnot

 
theorem squareMesh_unique_inner_edge {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) {z : Plane}
    (hz : z ∈ fresh) :
    ∃! P : Piece, P ∈ E(squareMesh δ fresh anchors) ∧ (z = P.1 ∨ z = P.2) ∧
      ¬ P.seg ⊆ modelCurve :=
  unique_inner_edge_at_fresh (two_le_meshCount δ) hfresh anchors hz

 
theorem squareMesh_isConnected_diff {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) {z₀ : Plane}
    (hz₀ : z₀ ∈ fresh) :
    IsConnected
      (Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing \ modelCurve) := by
  rw [squareMesh_pointSet]
  exact isConnected_cover_diff_modelCurve (two_le_meshCount δ) hfresh hz₀

end Schoenflies
