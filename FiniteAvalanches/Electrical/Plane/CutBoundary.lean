import FiniteAvalanches.Electrical.Plane.CutCoordinates

/-! The voltage-cut indicator, tested on actual rotation faces, produces an integer dual unit flow. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- Literal indicator of the original strict voltage sublevel. -/
noncomputable def voltageCutoff {V : Type*} (phi : V → ℝ) (t : ℝ) (x : V) : ℝ :=
  if phi x < t then 1 else 0

private theorem cut_edge_incidence {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (t : ℝ)
    (f : ArcFace R da db) (e : E) :
    ((if dualA R da db (.inl e) = f then voltageCutoff phi t (a e)-voltageCutoff phi t (b e) else 0)-
      (if dualB R da db (.inl e) = f then voltageCutoff phi t (a e)-voltageCutoff phi t (b e) else 0)) =
      -(if h : e ∈ crossingEdges a b phi t then
        ((if cutA R da db phi t ⟨e,h⟩ = f then (1 : ℝ) else 0)-
          (if cutB R da db phi t ⟨e,h⟩ = f then 1 else 0)) else 0) := by
  by_cases ha : phi (a e) < t
  · by_cases hb : phi (b e) < t
    · have hn : e ∉ crossingEdges a b phi t := by
        intro hm
        rcases (mem_crossingEdges a b phi t e).mp hm with hm | hm
        · exact not_le_of_gt hb hm.2
        · exact not_le_of_gt ha hm.2
      simp only [voltageCutoff,if_pos ha,if_pos hb,sub_self,ite_self,dif_neg hn,neg_zero]
    · have hm : e ∈ crossingEdges a b phi t :=
        (mem_crossingEdges a b phi t e).mpr (Or.inl ⟨ha,le_of_not_gt hb⟩)
      have hf := cut_faces_of_lt R da db phi t ⟨e,hm⟩ ha
      simp only [voltageCutoff,if_pos ha,if_neg hb,sub_zero,dif_pos hm,hf.1,hf.2]
      split_ifs <;> ring
  · by_cases hb : phi (b e) < t
    · have hm : e ∈ crossingEdges a b phi t :=
        (mem_crossingEdges a b phi t e).mpr (Or.inr ⟨hb,le_of_not_gt ha⟩)
      have hf := cut_faces_of_not_lt R da db phi t ⟨e,hm⟩ ha
      simp only [voltageCutoff,if_neg ha,if_pos hb,zero_sub,dif_pos hm,hf.1,hf.2]
      split_ifs <;> ring
    · have hn : e ∉ crossingEdges a b phi t := by
        intro hm
        rcases (mem_crossingEdges a b phi t e).mp hm with hm | hm
        · exact ha hm.1
        · exact hb hm.1
      simp only [voltageCutoff,if_neg ha,if_neg hb,sub_self,ite_self,dif_neg hn,neg_zero]

/-- The actual crossing-copy unit flow has one source and one sink at the closing-arc faces. -/
theorem cut_unitBoundary {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (f : ArcFace R da db) :
    unitBoundary (cutA R da db phi t) (cutB R da db phi t) Finset.univ f =
      (if arcRightFace R da db (.inr false) = f then 1 else 0)-
        (if arcLeftFace R da db (.inr false) = f then 1 else 0) := by
  have hqa : voltageCutoff phi t alpha = 1 := by simp only [voltageCutoff,hp0,if_pos ht0]
  have hqb : voltageCutoff phi t beta = 0 := by
    simp only [voltageCutoff,hp1,if_neg (not_lt.mpr ht1.le)]
  have hs := dualBoundary_primalGradient R alpha beta hne da db ha hb (voltageCutoff phi t) f
  simp only [copyBoundary,Fintype.sum_sum_type,Fintype.sum_unique,
    copyGradient,arcA,arcB,hqa,hqb,sub_zero] at hs
  rw [Finset.sum_congr rfl (fun e _ => cut_edge_incidence R da db phi t f e),
    Finset.sum_neg_distrib] at hs
  have hu : unitBoundary (cutA R da db phi t) (cutB R da db phi t) Finset.univ f =
      ∑ e, if h : e ∈ crossingEdges a b phi t then
        ((if cutA R da db phi t ⟨e,h⟩ = f then (1 : ℝ) else 0)-
          (if cutB R da db phi t ⟨e,h⟩ = f then 1 else 0)) else 0 := by
    rw [unitBoundary,Finset.univ_eq_attach,Finset.sum_attach_eq_sum_dite]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> rfl
  rw [hu]
  change -(∑ e, if h : e ∈ crossingEdges a b phi t then
    ((if cutA R da db phi t ⟨e,h⟩ = f then (1 : ℝ) else 0)-
      (if cutB R da db phi t ⟨e,h⟩ = f then 1 else 0)) else 0)+
    ((if arcRightFace R da db (.inr false) = f then 1 else 0)-
      (if arcLeftFace R da db (.inr false) = f then 1 else 0)) = 0 at hs
  linarith only [hs]

end FiniteAvalanches.Electrical.Plane
