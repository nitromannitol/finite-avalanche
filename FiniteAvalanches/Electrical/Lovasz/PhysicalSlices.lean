import PhysicalStreamCuts
import FiniteAvalanches.Electrical.Lovasz.PhysicalIntervals

                                                                               
                                                                             
                                                                                   

namespace FiniteAvalanches.Electrical.Lovasz
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.Plane
open FiniteAvalanches.Electrical.LovaszPhysical
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- Distinct normalized boundary values on a connected copied network give positive mass. -/
theorem mass_pos_of_normalized_boundary (J : CopiedGraph V E)
    (alpha beta : V) (hc : (supportGraph J.left J.right).Preconnected)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1) : 0 < mass J phi := by
  have hne : energy J.left J.right phi ≠ 0 := by
    intro hz
    have he := (energy_eq_zero_iff J.left J.right phi).mp hz
    have h := eq_of_reachable J.left J.right phi he (hc alpha beta)
    rw [hp0, hp1] at h
    exact zero_ne_one h
  exact lt_of_le_of_ne (energy_nonneg J.left J.right phi) hne.symm

/-- The same physical path retains every consecutive actual-face row when
current conservation determines its monotone stream orientation. -/
theorem physical_cut_monotone_rows (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hgeneric : ∀ x, phi x ≠ t) :
    ∃ m : ℕ, ∃ vertices : Fin (m + 1) → A.embedding.Face,
      ∃ copies : Fin m ≃ CutCopy J.left J.right phi t,
        (∀ i : Fin m,
          (A.embedding.rightFace (.inl (copies i).val) = vertices i.castSucc ∧
            A.embedding.leftFace (.inl (copies i).val) = vertices i.succ) ∨
          (A.embedding.leftFace (.inl (copies i).val) = vertices i.castSucc ∧
            A.embedding.rightFace (.inl (copies i).val) = vertices i.succ)) ∧
        ((psi (vertices 0) = 0 ∧ psi (vertices (Fin.last m)) = mass J phi ∧
            ∀ i : Fin m, psi (vertices i.castSucc) < psi (vertices i.succ)) ∨
          (psi (vertices 0) = mass J phi ∧ psi (vertices (Fin.last m)) = 0 ∧
            ∀ i : Fin m, psi (vertices i.succ) < psi (vertices i.castSucc))) := by
  obtain ⟨m, vertices, _, copies, hrows, hends⟩ := physical_voltage_cut_path
    J D hc alpha beta A phi hp0 hp1 hh t ht0 ht1 hgeneric
  obtain ⟨hsum, hpos⟩ := cut_stream_variation
    J D alpha beta hne A phi hp0 hp1 hh psi hpsi t ht0 ht1 m vertices copies hrows
  refine ⟨m, vertices, copies, hrows, ?_⟩
  rcases hends with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · have hz : psi (vertices 0) = 0 := by rw [← h0]; exact hpsi.2.2.1
    have hM : psi (vertices (Fin.last m)) = mass J phi := by rw [← h1]; exact hpsi.2.2.2
    refine Or.inl ⟨hz, hM, ?_⟩
    apply adjacent_pos_of_total_variation m (psi ∘ vertices) _ hpos
    simpa only [Function.comp_apply, hz, hM, sub_zero] using hsum
  · have hM : psi (vertices 0) = mass J phi := by rw [← h1]; exact hpsi.2.2.2
    have hz : psi (vertices (Fin.last m)) = 0 := by rw [← h0]; exact hpsi.2.2.1
    refine Or.inr ⟨hM, hz, ?_⟩
    have hv : (∑ i : Fin m, |(-psi (vertices i.succ)) - (-psi (vertices i.castSucc))|) =
        (-psi (vertices (Fin.last m))) - (-psi (vertices 0)) := by
      simpa only [neg_sub_neg, abs_sub_comm, hM, hz, neg_zero, zero_sub, neg_neg] using hsum
    have hp (i : Fin m) : 0 < |(-psi (vertices i.succ)) - (-psi (vertices i.castSucc))| := by
      simpa only [neg_sub_neg, abs_sub_comm] using hpos i
    have h := adjacent_pos_of_total_variation m (fun i => -psi (vertices i)) hv hp
    exact fun i => neg_lt_neg_iff.mp (h i)

/-- Actual consecutive face rows identify each original closed square slice. -/
theorem physical_copy_closed_slice (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (alpha beta : V) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (psi : A.embedding.Face → ℝ) (t : ℝ) (m : ℕ)
    (vertices : Fin (m + 1) → A.embedding.Face)
    (copies : Fin m ≃ CutCopy J.left J.right phi t)
    (hrows : ∀ i : Fin m,
      (A.embedding.rightFace (.inl (copies i).val) = vertices i.castSucc ∧
        A.embedding.leftFace (.inl (copies i).val) = vertices i.succ) ∨
      (A.embedding.leftFace (.inl (copies i).val) = vertices i.castSucc ∧
        A.embedding.rightFace (.inl (copies i).val) = vertices i.succ))
    (i : Fin m) (u : ℝ) :
    (t, u) ∈ edgeSquare D alpha beta A phi psi (copies i).val ↔
      u ∈ Set.Icc (min (psi (vertices i.castSucc)) (psi (vertices i.succ)))
        (max (psi (vertices i.castSucc)) (psi (vertices i.succ))) := by
  have hv := cut_voltage_bounds J.left J.right phi t (copies i)
  simp only [edgeSquare, Set.mem_prod, Set.mem_Icc]
  rcases hrows i with ⟨hr, hl⟩ | ⟨hl, hr⟩
  · rw [hr, hl, min_comm (psi (vertices i.succ)), max_comm (psi (vertices i.succ))]
    exact and_iff_right hv
  · rw [hl, hr]
    exact and_iff_right hv

/-- Actual consecutive face rows identify each original open square slice. -/
theorem physical_copy_open_stream (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (alpha beta : V) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (psi : A.embedding.Face → ℝ) (t : ℝ) (m : ℕ)
    (vertices : Fin (m + 1) → A.embedding.Face)
    (copies : Fin m ≃ CutCopy J.left J.right phi t)
    (hrows : ∀ i : Fin m,
      (A.embedding.rightFace (.inl (copies i).val) = vertices i.castSucc ∧
        A.embedding.leftFace (.inl (copies i).val) = vertices i.succ) ∨
      (A.embedding.leftFace (.inl (copies i).val) = vertices i.castSucc ∧
        A.embedding.rightFace (.inl (copies i).val) = vertices i.succ))
    (i : Fin m) (z : ℝ × ℝ)
    (hz : z ∈ interior (edgeSquare D alpha beta A phi psi (copies i).val)) :
    z.2 ∈ Set.Ioo (min (psi (vertices i.castSucc)) (psi (vertices i.succ)))
      (max (psi (vertices i.castSucc)) (psi (vertices i.succ))) := by
  simp only [edgeSquare, interior_prod_eq, interior_Icc] at hz
  rcases hrows i with ⟨hr, hl⟩ | ⟨hl, hr⟩
  · rw [hr, hl, min_comm (psi (vertices i.succ)), max_comm (psi (vertices i.succ))] at hz
    exact hz.2
  · rw [hl, hr] at hz
    exact hz.2

/-- A generic voltage slice is covered by actual original square IDs, including
both closed stream endpoints. The cut paths are produced internally. -/
theorem physical_generic_slice_cover (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi)
    (t u : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hgeneric : ∀ x, phi x ≠ t)
    (hu0 : 0 ≤ u) (huM : u ≤ mass J phi) :
    ∃ e : E, (t, u) ∈ edgeSquare D alpha beta A phi psi e := by
  obtain ⟨m, vertices, copies, hrows, hmode⟩ := physical_cut_monotone_rows
    J D hc alpha beta hne A phi hp0 hp1 hh psi hpsi t ht0 ht1 hgeneric
  have hM := mass_pos_of_normalized_boundary J alpha beta hc phi hp0 hp1
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hn
    subst m
    have hlast : Fin.last 0 = (0 : Fin 1) := rfl
    rw [hlast] at hmode
    rcases hmode with ⟨h0, h1, _⟩ | ⟨h0, h1, _⟩ <;> linarith only [hM, h0, h1]
  have hstep : (∀ i : Fin m, psi (vertices i.castSucc) < psi (vertices i.succ)) ∨
      (∀ i : Fin m, psi (vertices i.succ) < psi (vertices i.castSucc)) :=
    hmode.elim (fun h => Or.inl h.2.2) (fun h => Or.inr h.2.2)
  have hu : u ∈ Set.Icc (min (psi (vertices 0)) (psi (vertices (Fin.last m))))
      (max (psi (vertices 0)) (psi (vertices (Fin.last m)))) := by
    rcases hmode with ⟨h0, h1, _⟩ | ⟨h0, h1, _⟩
    · rw [h0, h1, min_eq_left hM.le, max_eq_right hM.le]
      exact ⟨hu0, huM⟩
    · rw [h0, h1, min_eq_right hM.le, max_eq_left hM.le]
      exact ⟨hu0, huM⟩
  obtain ⟨i, hi⟩ := fin_path_unordered_interval_cover m hm (fun i => psi (vertices i)) hstep u hu
  exact ⟨(copies i).val, (physical_copy_closed_slice J D alpha beta A phi psi t m
    vertices copies hrows i u).mpr hi⟩

/-- Finite closed-square coverage extends generic slices through every vertex
voltage level and both voltage boundaries; zero-current point squares remain. -/
theorem rectangle_subset_physical_square_union (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi) :
    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (mass J phi) ⊆
      ⋃ e : E, edgeSquare D alpha beta A phi psi e := by
  let U := ⋃ e : E, edgeSquare D alpha beta A phi psi e
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun _ => isClosed_Icc.prod isClosed_Icc)
  have hG : {t : ℝ | 0 < t ∧ t < 1 ∧ ∀ x : V, phi x ≠ t} ×ˢ Set.Icc (0 : ℝ) (mass J phi) ⊆ U := by
    intro z hz
    obtain ⟨e, he⟩ := physical_generic_slice_cover J D hc alpha beta hne A phi hp0 hp1 hh psi hpsi
      z.1 z.2 hz.1.1 hz.1.2.1 hz.1.2.2 hz.2.1 hz.2.2
    exact Set.mem_iUnion.mpr ⟨e, he⟩
  have hclosure := closure_minimal hG hU
  rw [closure_prod_eq, closure_generic_voltage_levels, isClosed_Icc.closure_eq] at hclosure
  exact hclosure

/-- Distinct original physical square interiors are disjoint, using the actual
monotone cut path near their hypothetical overlap and no supplied packing premise. -/
theorem physical_square_interiors_disjoint_of_stream (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi)
    (e f : E) (hef : e ≠ f) :
    Disjoint (interior (edgeSquare D alpha beta A phi psi e))
      (interior (edgeSquare D alpha beta A phi psi f)) := by
  apply Set.disjoint_left.mpr
  intro z hze hzf
  have hze' := hze
  have hzf' := hzf
  simp only [edgeSquare, interior_prod_eq, interior_Icc] at hze' hzf'
  let lo := max (min (phi (J.left e)) (phi (J.right e))) (min (phi (J.left f)) (phi (J.right f)))
  let hi := min (max (phi (J.left e)) (phi (J.right e))) (max (phi (J.left f)) (phi (J.right f)))
  have hzlo : lo < z.1 := max_lt hze'.1.1 hzf'.1.1
  have hzhi : z.1 < hi := lt_min hze'.1.2 hzf'.1.2
  obtain ⟨t, htlo, hthi, hgeneric⟩ := exists_generic_voltage phi lo hi (hzlo.trans hzhi)
  have hv := voltage_range J.left J.right alpha beta hc phi hp0 hp1 hh
  have ht0 : 0 < t :=
    ((le_min (hv (J.left e)).1 (hv (J.right e)).1).trans (le_max_left _ _)).trans_lt htlo
  have ht1 : t < 1 :=
    hthi.trans_le ((min_le_left _ _).trans (max_le (hv (J.left e)).2 (hv (J.right e)).2))
  let ce : CutCopy J.left J.right phi t := ⟨e, mem_crossingEdges_of_voltage_interior J.left J.right phi t e
    ⟨(le_max_left _ _).trans_lt htlo, hthi.trans_le (min_le_left _ _)⟩⟩
  let cf : CutCopy J.left J.right phi t := ⟨f, mem_crossingEdges_of_voltage_interior J.left J.right phi t f
    ⟨(le_max_right _ _).trans_lt htlo, hthi.trans_le (min_le_right _ _)⟩⟩
  obtain ⟨m, vertices, copies, hrows, hmode⟩ := physical_cut_monotone_rows
    J D hc alpha beta hne A phi hp0 hp1 hh psi hpsi t ht0 ht1 hgeneric
  let i := copies.symm ce
  let j := copies.symm cf
  have hie : (copies i).val = e := congrArg Subtype.val (copies.apply_symm_apply ce)
  have hjf : (copies j).val = f := congrArg Subtype.val (copies.apply_symm_apply cf)
  have hij : i ≠ j := fun h => hef (hie.symm.trans ((congrArg (fun k => (copies k).val) h).trans hjf))
  have hstep : (∀ k : Fin m, psi (vertices k.castSucc) < psi (vertices k.succ)) ∨
      (∀ k : Fin m, psi (vertices k.succ) < psi (vertices k.castSucc)) :=
    hmode.elim (fun h => Or.inl h.2.2) (fun h => Or.inr h.2.2)
  have hd := fin_path_unordered_interval_disjoint m (fun k => psi (vertices k)) hstep i j hij
  apply Set.disjoint_left.mp hd
  · apply physical_copy_open_stream J D alpha beta A phi psi t m vertices copies hrows i z
    rw [hie]
    exact hze
  · apply physical_copy_open_stream J D alpha beta A phi psi t m vertices copies hrows j z
    rw [hjf]
    exact hzf

end
end FiniteAvalanches.Electrical.Lovasz

#print axioms FiniteAvalanches.Electrical.Lovasz.mass_pos_of_normalized_boundary
#print axioms FiniteAvalanches.Electrical.Lovasz.physical_cut_monotone_rows
#print axioms FiniteAvalanches.Electrical.Lovasz.physical_generic_slice_cover
#print axioms FiniteAvalanches.Electrical.Lovasz.rectangle_subset_physical_square_union
#print axioms FiniteAvalanches.Electrical.Lovasz.physical_square_interiors_disjoint_of_stream
