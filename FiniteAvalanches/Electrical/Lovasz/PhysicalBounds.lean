import FiniteAvalanches.Electrical.Lovasz.PhysicalSlices

/-! Stream bounds and exact closed coverage, including zero-current copies.
Nonzero copies are bounded by their actual monotone cut paths; zero-copy values
are propagated through the registered connected physical dual. -/

namespace FiniteAvalanches.Electrical.Lovasz
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.Plane
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- Both actual side faces of a nonzero-current original copy are bounded by a
generic cut path in which that exact copy occurs. -/
theorem physical_nonzero_copy_stream_bounds (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi)
    (e : E) (he : phi (J.left e) ≠ phi (J.right e)) :
    (0 ≤ psi (A.embedding.rightFace (.inl e)) ∧ psi (A.embedding.rightFace (.inl e)) ≤ mass J phi) ∧
    (0 ≤ psi (A.embedding.leftFace (.inl e)) ∧ psi (A.embedding.leftFace (.inl e)) ≤ mass J phi) := by
  have hgap : min (phi (J.left e)) (phi (J.right e)) < max (phi (J.left e)) (phi (J.right e)) := by
    rcases lt_or_gt_of_ne he with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  obtain ⟨t, htlo, hthi, hgeneric⟩ := exists_generic_voltage phi _ _ hgap
  have hv := voltage_range J.left J.right alpha beta hc phi hp0 hp1 hh
  have ht0 : 0 < t := (le_min (hv (J.left e)).1 (hv (J.right e)).1).trans_lt htlo
  have ht1 : t < 1 := hthi.trans_le (max_le (hv (J.left e)).2 (hv (J.right e)).2)
  let ce : CutCopy J.left J.right phi t :=
    ⟨e, mem_crossingEdges_of_voltage_interior J.left J.right phi t e ⟨htlo, hthi⟩⟩
  obtain ⟨m, vertices, copies, hrows, hmode⟩ := physical_cut_monotone_rows
    J D hc alpha beta hne A phi hp0 hp1 hh psi hpsi t ht0 ht1 hgeneric
  let i := copies.symm ce
  have hie : (copies i).val = e := congrArg Subtype.val (copies.apply_symm_apply ce)
  have hM := (mass_pos_of_normalized_boundary J alpha beta hc phi hp0 hp1).le
  have hstep : (∀ k : Fin m, psi (vertices k.castSucc) < psi (vertices k.succ)) ∨
      (∀ k : Fin m, psi (vertices k.succ) < psi (vertices k.castSucc)) :=
    hmode.elim (fun h => Or.inl h.2.2) (fun h => Or.inr h.2.2)
  have hb (k : Fin (m + 1)) : 0 ≤ psi (vertices k) ∧ psi (vertices k) ≤ mass J phi := by
    have h := fin_path_vertex_bounds m (fun k => psi (vertices k)) hstep k
    rcases hmode with ⟨h0, h1, _⟩ | ⟨h0, h1, _⟩
    · simpa only [h0, h1, min_eq_left hM, max_eq_right hM] using h
    · simpa only [h0, h1, min_eq_right hM, max_eq_left hM] using h
  have hrow := hrows i
  rw [hie] at hrow
  rcases hrow with ⟨hr, hl⟩ | ⟨hl, hr⟩
  · rw [hr, hl]
    exact ⟨hb i.castSucc, hb i.succ⟩
  · rw [hr, hl]
    exact ⟨hb i.succ, hb i.castSucc⟩

/-- Every actual face stream lies in the normalized interval. Zero-current dual
steps preserve its value, and nonzero steps already have both ends bounded. -/
theorem physical_stream_bounds_of_stream (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi) :
    ∀ F, 0 ≤ psi F ∧ psi F ≤ mass J phi := by
  let B := fun F : A.embedding.Face => 0 ≤ psi F ∧ psi F ≤ mass J phi
  have hM := (mass_pos_of_normalized_boundary J alpha beta hc phi hp0 hp1).le
  have hpair (z : E ⊕ Unit) :
      psi (A.embedding.rightFace z) = psi (A.embedding.leftFace z) ∨
        (B (A.embedding.rightFace z) ∧ B (A.embedding.leftFace z)) := by
    cases z with
    | inl e =>
      by_cases he : phi (J.left e) = phi (J.right e)
      · apply Or.inl
        have h := hpsi.1 e
        rw [he, sub_self] at h
        exact (sub_eq_zero.mp h).symm
      · exact Or.inr (physical_nonzero_copy_stream_bounds
          J D hc alpha beta hne A phi hp0 hp1 hh psi hpsi e he)
    | inr u =>
      cases u
      apply Or.inr
      change (0 ≤ psi (A.embedding.rightFace (.inr ())) ∧ psi (A.embedding.rightFace (.inr ())) ≤ mass J phi) ∧
        (0 ≤ psi (A.embedding.leftFace (.inr ())) ∧ psi (A.embedding.leftFace (.inr ())) ≤ mass J phi)
      rw [hpsi.2.2.1, hpsi.2.2.2]
      exact ⟨⟨le_rfl, hM⟩, ⟨hM, le_rfl⟩⟩
  let G := supportGraph A.embedding.rightFace A.embedding.leftFace
  have step {F H : A.embedding.Face} (hFH : G.Adj F H) (hF : B F) : B H := by
    obtain ⟨_, z, hz⟩ := hFH
    rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hpair z with he | hb
      · simpa only [B, he] using hF
      · exact hb.2
    · rcases hpair z with he | hb
      · simpa only [B, he] using hF
      · exact hb.1
  have walks {F H : A.embedding.Face} (p : G.Walk F H) : B F → B H := by
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hF => ih (step h hF)
  letI : Nonempty (E ⊕ Unit) := ⟨.inr ()⟩
  have haug : (supportGraph (augmentedGraph J alpha beta).left
      (augmentedGraph J alpha beta).right).Preconnected := hc.mono (by
    intro x y h
    obtain ⟨hne, e, he⟩ := h
    exact ⟨hne, .inl e, he⟩)
  have hd := FiniteAvalanches.External.finite_plane_dual_connected
    (augmentedGraph J alpha beta) A.embedding.drawing A.embedding.edgeChart haug
  intro F
  obtain ⟨p⟩ := hd (A.embedding.rightFace (.inr ())) F
  apply walks p
  change 0 ≤ psi (A.embedding.rightFace (.inr ())) ∧ psi (A.embedding.rightFace (.inr ())) ≤ mass J phi
  rw [hpsi.2.2.1]
  exact ⟨le_rfl, hM⟩

/-- Actual physical squares have disjoint interiors and equal the full closed
rectangle, retaining zero-current points and every copied edge. Stream
existence remains a separate obligation, and no tiling result is assumed. -/
theorem physical_tiling_of_stream (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi) :
    (∀ F, 0 ≤ psi F ∧ psi F ≤ mass J phi) ∧
    (∀ e f : E, e ≠ f → Disjoint (interior (edgeSquare D alpha beta A phi psi e))
      (interior (edgeSquare D alpha beta A phi psi f))) ∧
    (⋃ e : E, edgeSquare D alpha beta A phi psi e) = Set.Icc 0 1 ×ˢ Set.Icc 0 (mass J phi) := by
  have hs := physical_stream_bounds_of_stream J D hc alpha beta hne A phi hp0 hp1 hh psi hpsi
  have hv := voltage_range J.left J.right alpha beta hc phi hp0 hp1 hh
  refine ⟨hs, physical_square_interiors_disjoint_of_stream J D hc alpha beta hne A phi hp0 hp1 hh psi hpsi, ?_⟩
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro e z hz
    change z.1 ∈ Set.Icc _ _ ∧ z.2 ∈ Set.Icc _ _ at hz
    exact ⟨⟨(le_min (hv _).1 (hv _).1).trans hz.1.1,
        hz.1.2.trans (max_le (hv _).2 (hv _).2)⟩,
      ⟨(le_min (hs _).1 (hs _).1).trans hz.2.1,
        hz.2.2.trans (max_le (hs _).2 (hs _).2)⟩⟩
  · exact rectangle_subset_physical_square_union J D hc alpha beta hne A phi hp0 hp1 hh psi hpsi

end
end FiniteAvalanches.Electrical.Lovasz

#print axioms FiniteAvalanches.Electrical.Lovasz.physical_nonzero_copy_stream_bounds
#print axioms FiniteAvalanches.Electrical.Lovasz.physical_stream_bounds_of_stream
#print axioms FiniteAvalanches.Electrical.Lovasz.physical_tiling_of_stream
