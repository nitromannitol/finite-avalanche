import PhysicalVoltageCuts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Current conservation fixes the stream direction of an actual physical voltage cut. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LovaszPhysical
open StatementGeometry Source BSST
open scoped Classical BigOperators
noncomputable section

/-- The stream changes along a finite path telescope to the endpoint difference. -/
theorem sum_adjacent_sub (m : ℕ) (f : Fin (m+1) → ℝ) :
    (∑ i : Fin m, (f i.succ-f i.castSucc)) = f (Fin.last m)-f 0 := by
  rw [Finset.sum_sub_distrib]
  have h0 := Fin.sum_univ_succ f
  have h1 := Fin.sum_univ_castSucc f
  linarith only [h0,h1]

/-- Equality of total variation and endpoint increase forces every nonzero step upwards. -/
theorem adjacent_pos_of_total_variation (m : ℕ) (f : Fin (m+1) → ℝ)
    (hvariation : (∑ i : Fin m, |f i.succ-f i.castSucc|) = f (Fin.last m)-f 0)
    (hpos : ∀ i : Fin m, 0 < |f i.succ-f i.castSucc|) :
    ∀ i : Fin m, f i.castSucc < f i.succ := by
  let d : Fin m → ℝ := fun i => f i.succ-f i.castSucc
  have hzero : (∑ i : Fin m, (|d i|-d i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    change (∑ i : Fin m, |f i.succ-f i.castSucc|)-
      (∑ i : Fin m, (f i.succ-f i.castSucc)) = 0
    rw [hvariation,sum_adjacent_sub,sub_self]
  have heq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_hi : i ∈ (Finset.univ : Finset (Fin m))) => sub_nonneg.mpr (le_abs_self (d i)))).mp hzero
  intro i
  have hi : |d i| = d i := sub_eq_zero.mp (heq i (Finset.mem_univ i))
  have hp : 0 < d i := hi ▸ hpos i
  exact sub_pos.mp hp

variable {V E : Type} [Fintype V] [Fintype E]

/-- All original crossing IDs account for the full mass in any enumerated physical cut path. -/
theorem cut_stream_variation (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (alpha beta : V) (hne : alpha ≠ beta) (A : OuterArc D alpha beta)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (m : ℕ) (vertices : Fin (m+1) → A.embedding.Face)
    (copies : Fin m ≃ {e : E // e ∈ Plane.crossingEdges J.left J.right phi t})
    (hrows : ∀ i : Fin m,
      (A.embedding.rightFace (.inl (copies i).val) = vertices i.castSucc ∧
        A.embedding.leftFace (.inl (copies i).val) = vertices i.succ) ∨
      (A.embedding.leftFace (.inl (copies i).val) = vertices i.castSucc ∧
        A.embedding.rightFace (.inl (copies i).val) = vertices i.succ)) :
    (∑ i : Fin m, |psi (vertices i.succ)-psi (vertices i.castSucc)|) = mass J phi ∧
      ∀ i : Fin m, 0 < |psi (vertices i.succ)-psi (vertices i.castSucc)| := by
  have hj (i : Fin m) : |psi (vertices i.succ)-psi (vertices i.castSucc)| =
      |phi (J.left (copies i).val)-phi (J.right (copies i).val)| := by
    have hi := hpsi.1 (copies i).val
    rcases hrows i with ⟨hr,hl⟩ | ⟨hl,hr⟩
    · rw [hr,hl] at hi
      exact congrArg abs hi
    · rw [hr,hl] at hi
      rw [abs_sub_comm]
      exact congrArg abs hi
  constructor
  · rw [Finset.sum_congr rfl (fun i _ => hj i)]
    rw [copies.sum_comp (fun e => |phi (J.left e.val)-phi (J.right e.val)|)]
    rw [Finset.sum_coe_sort (Plane.crossingEdges J.left J.right phi t)
      (fun e => |phi (J.left e)-phi (J.right e)|)]
    exact Plane.sum_crossing_current_eq_energy J.left J.right alpha beta hne phi hp0 hp1 hh t ht0 ht1
  · intro i
    rw [hj i]
    apply abs_pos.mpr
    apply sub_ne_zero.mpr
    rcases (Plane.mem_crossingEdges _ _ _ _ _).mp (copies i).property with ⟨hl,hr⟩ | ⟨hr,hl⟩
    · exact ne_of_lt (hl.trans_le hr)
    · exact Ne.symm (ne_of_lt (hr.trans_le hl))

/-- The actual cut path of an existing physical stream is strictly monotone in one orientation.
No signed cycle ordering or square-packing premise is supplied. -/
theorem physical_cut_monotone_stream (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hgeneric : ∀ x, phi x ≠ t) :
    ∃ m : ℕ, ∃ vertices : Fin (m+1) → A.embedding.Face,
      Function.Injective vertices ∧
      ∃ copies : Fin m ≃ {e : E // e ∈ Plane.crossingEdges J.left J.right phi t},
        (∀ i : Fin m,
          |psi (vertices i.succ)-psi (vertices i.castSucc)| =
            |phi (J.left (copies i).val)-phi (J.right (copies i).val)|) ∧
        ((psi (vertices 0) = 0 ∧ psi (vertices (Fin.last m)) = mass J phi ∧
            ∀ i : Fin m, psi (vertices i.castSucc) < psi (vertices i.succ)) ∨
          (psi (vertices 0) = mass J phi ∧ psi (vertices (Fin.last m)) = 0 ∧
            ∀ i : Fin m, psi (vertices i.succ) < psi (vertices i.castSucc))) := by
  obtain ⟨m,vertices,hinj,copies,hrows,hends⟩ :=
    physical_voltage_cut_path J D hc alpha beta A phi hp0 hp1 hh t ht0 ht1 hgeneric
  have hj (i : Fin m) : |psi (vertices i.succ)-psi (vertices i.castSucc)| =
      |phi (J.left (copies i).val)-phi (J.right (copies i).val)| := by
    have hi := hpsi.1 (copies i).val
    rcases hrows i with ⟨hr,hl⟩ | ⟨hl,hr⟩
    · rw [hr,hl] at hi
      exact congrArg abs hi
    · rw [hr,hl] at hi
      rw [abs_sub_comm]
      exact congrArg abs hi
  obtain ⟨hsum,hpos⟩ := cut_stream_variation J D alpha beta hne A phi hp0 hp1 hh psi hpsi
    t ht0 ht1 m vertices copies hrows
  refine ⟨m,vertices,hinj,copies,hj,?_⟩
  rcases hends with ⟨h0,h1⟩ | ⟨h1,h0⟩
  · have hp0' : psi (vertices 0) = 0 := by rw [← h0]; exact hpsi.2.2.1
    have hp1' : psi (vertices (Fin.last m)) = mass J phi := by rw [← h1]; exact hpsi.2.2.2
    refine Or.inl ⟨hp0',hp1',?_⟩
    apply adjacent_pos_of_total_variation m (psi ∘ vertices) _ hpos
    simpa only [Function.comp_apply,hp0',hp1',sub_zero] using hsum
  · have hp0' : psi (vertices 0) = mass J phi := by rw [← h1]; exact hpsi.2.2.2
    have hp1' : psi (vertices (Fin.last m)) = 0 := by rw [← h0]; exact hpsi.2.2.1
    refine Or.inr ⟨hp0',hp1',?_⟩
    have hvariation : (∑ i : Fin m, |(-psi (vertices i.succ))-(-psi (vertices i.castSucc))|) =
        (-psi (vertices (Fin.last m)))-(-psi (vertices 0)) := by
      simpa only [neg_sub_neg,abs_sub_comm,hp0',hp1',neg_zero,zero_sub,neg_neg] using hsum
    have hpos' (i : Fin m) : 0 < |(-psi (vertices i.succ))-(-psi (vertices i.castSucc))| := by
      simpa only [neg_sub_neg,abs_sub_comm] using hpos i
    have hm := adjacent_pos_of_total_variation m (fun i => -psi (vertices i)) hvariation hpos'
    intro i
    exact neg_lt_neg_iff.mp (hm i)

end
end FiniteAvalanches.Electrical.LovaszPhysical

#print axioms FiniteAvalanches.Electrical.LovaszPhysical.sum_adjacent_sub
#print axioms FiniteAvalanches.Electrical.LovaszPhysical.adjacent_pos_of_total_variation
#print axioms FiniteAvalanches.Electrical.LovaszPhysical.cut_stream_variation
#print axioms FiniteAvalanches.Electrical.LovaszPhysical.physical_cut_monotone_stream
