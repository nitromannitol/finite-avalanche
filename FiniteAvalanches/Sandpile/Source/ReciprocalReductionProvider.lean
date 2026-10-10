import FiniteAvalanches.Sandpile.Source.RadiusCutPast

/-! The exact reciprocal-radius reduction, with one universal constant chosen
before both integer scales. No avalanche-finiteness assumption is used. -/
namespace FiniteAvalanches.Sandpile.Source
open LatticeProb MeasureTheory FiniteAvalanches FiniteAvalanches.Sandpile
open SourceCounting Trees.Lattice TreeMeasurability11
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal BigOperators
noncomputable section

theorem connector_endpoints_in_box {r : ℕ} (hr : 2 ≤ r)
    (j : Fin r ⊕ FiniteWired.Direction) :
    ∃ x y : Site2, (connectorEdge r j).val = s(x,y) ∧
      x ∈ boxSites r ∧ y ∈ boxSites r := by
  have hm : connectorCopy r r le_rfl j ∈ sourceEdges r r le_rfl := by
    cases j with
    | inl k => exact horizontalEdge_mem le_rfl k
    | inr d => exact directionEdge_mem_sourceEdges hr le_rfl d
  obtain ⟨x,y,he,hx,hy⟩ := sourceEdges_endpoints_in_box hr le_rfl hm
  refine ⟨FiniteWired.site x,FiniteWired.site y,?_,hx,hy⟩
  rw [← original_connector_copy hr le_rfl j]
  obtain ⟨i,hi⟩ := sourceEdges_no_exit hr le_rfl hm
  rw [hi] at he ⊢
  change (some i.val.1,some i.val.2) = (some x,some y) at he
  have hl := Option.some.inj (congrArg Prod.fst he)
  have hu := Option.some.inj (congrArg Prod.snd he)
  change s(FiniteWired.site i.val.1,FiniteWired.site i.val.2) = _
  rw [hl,hu]

theorem source_marks_eq_literal (r : ℕ) :
    sourceMarks r = insert (0 : Site2) (insert ((r : ℤ) • unit 0) (nbrFinset 0)) := by
  have ha : axisSite r = (r : ℤ) • unit 0 := by
    funext i
    fin_cases i <;> simp [axisSite,unit]
  rw [sourceMarks,ha,Finset.insert_comm]

end
end FiniteAvalanches.Sandpile.Source

namespace FiniteAvalanchesProofs.ReciprocalReduction
open LatticeProb MeasureTheory FiniteAvalanches FiniteAvalanches.Sandpile
open SourceCounting Trees.Lattice TreeMeasurability11 FiniteAvalanches.Sandpile.Source
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal BigOperators
noncomputable section

/-- Complete exact frozen statement, proved against the actual laws. -/
theorem reciprocal_reduction :
    ∃ C : ℝ, ∀ r : ℕ, 2 ≤ r → ∀ M : ℕ, r+2 ≤ M →
      (infiniteVolumeLaw : Measure StableField).real
          {η | ENNReal.ofReal (M : ℝ) < extendedCount (radius η 0)} ≤
        (∫ T, infiniteReciprocal
          (insert (0 : Site2) (insert ((r : ℤ) • unit 0) (nbrFinset 0)))
          (Finset.insert_nonempty _ _) T ∂endedUST) +
        C*(r : ℝ)*((M : ℝ)-(r : ℝ)) ^ (-(1/3 : ℝ)) := by
  obtain ⟨C,hC,hcut⟩ := exists_cut_escape_bound
  refine ⟨6*C,?_⟩
  intro r hr M hM
  have hsum : (∑ j : Fin r ⊕ FiniteWired.Direction,
      endedUST.real (infiniteCutEscape 0 (connectorEdge r j) M)) ≤
      (6*C)*(r : ℝ)*((M : ℝ)-(r : ℝ)) ^ (-(1/3 : ℝ)) := by
    have hj : ∀ j : Fin r ⊕ FiniteWired.Direction,
        endedUST.real (infiniteCutEscape 0 (connectorEdge r j) M) ≤
          2*C*((M : ℝ)-(r : ℝ)) ^ (-(1/3 : ℝ)) := by
      intro j
      obtain ⟨x,y,hf,hx,hy⟩ := connector_endpoints_in_box hr j
      exact hcut r M hM (connectorEdge r j) x y hf hx hy
    calc
      _ ≤ ∑ _j : Fin r ⊕ FiniteWired.Direction,
          2*C*((M : ℝ)-(r : ℝ)) ^ (-(1/3 : ℝ)) :=
        Finset.sum_le_sum (fun j _ => hj j)
      _ = ((r : ℝ)+4)*(2*C*((M : ℝ)-(r : ℝ)) ^ (-(1/3 : ℝ))) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_sum,Fintype.card_fin,
          Fintype.card_prod,Fintype.card_bool,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,nsmul_eq_mul]
        ring
      _ ≤ (3*(r : ℝ))*(2*C*((M : ℝ)-(r : ℝ)) ^ (-(1/3 : ℝ))) := by
        apply mul_le_mul_of_nonneg_right
        · have hrreal : 2 ≤ (r : ℝ) := by exact_mod_cast hr
          linarith only [hrreal]
        · have hgap : 0 ≤ (M : ℝ)-(r : ℝ) := by
            exact_mod_cast (show (0 : ℤ) ≤ (M : ℤ)-(r : ℤ) by omega)
          exact mul_nonneg (mul_nonneg (by norm_num) hC.le) (Real.rpow_nonneg hgap _)
      _ = _ := by ring
  have h := (infinite_radius_probability_le_connector hr (M := M)).trans (add_le_add le_rfl hsum)
  rw [FiniteAvalanches.Probability.real_radius_tail_eq_floor 0 (M : ℝ) (by positivity),
    Nat.floor_natCast]
  simpa only [source_marks_eq_literal] using h

#print axioms reciprocal_reduction
#print axioms FiniteAvalanches.Sandpile.Source.connector_endpoints_in_box
end
end FiniteAvalanchesProofs.ReciprocalReduction
