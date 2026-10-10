import FiniteAvalanches.Trees.Lattice.PastBoundary

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.PastTail
open LatticeProb SimpleGraph
open scoped Classical
noncomputable section

/-- Integer indicator of membership in the specified actual primal vertex set. -/
def cutIndicator (A : Set (Site 2)) (x : Site 2) : ℤ := if x ∈ A then 1 else 0

/-- Rotated signed membership difference on a base-named dual edge. Its nonzero
support is exactly the full crossed primal boundary; the sign accounts for the
quarter turn between the primal and dual once-oriented edges. -/
def dualCutCurrent (A : Set (Site 2)) (p : Site 2 × Fin 2) : ℤ :=
  if p.2 = 0 then
    cutIndicator A (dualBase p).1 - cutIndicator A ((dualBase p).1 + unit (dualBase p).2)
  else
    cutIndicator A ((dualBase p).1 + unit (dualBase p).2) - cutIndicator A (dualBase p).1

theorem dualCutCurrent_ne_zero_iff (A : Set (Site 2)) (p : Site 2 × Fin 2) :
    dualCutCurrent A p ≠ 0 ↔
      (((dualBase p).1 ∈ A ∧ (dualBase p).1 + unit (dualBase p).2 ∉ A) ∨
        ((dualBase p).1 ∉ A ∧ (dualBase p).1 + unit (dualBase p).2 ∈ A)) := by
  unfold dualCutCurrent cutIndicator
  split_ifs <;> simp_all

/-- Literal divergence cancellation at every dual vertex: the four membership
increments telescope around its primal unit square. No plane-separation premise. -/
theorem dualCutCurrent_divergence_zero (A : Set (Site 2)) (y : Site 2) :
    dualCutCurrent A (y, 0) + dualCutCurrent A (y, 1) -
      dualCutCurrent A (y - unit 0, 0) -
      dualCutCurrent A (y - unit 1, 1) = 0 := by
  simp only [dualCutCurrent, dualBase]
  norm_num
  rw [add_right_comm y (unit 0) (unit 1)]
  omega

/-- Every dual boundary edge entering a dual vertex has another boundary edge
there. This is stated on all four original incident edge IDs, with no filtering. -/
theorem dualCutCurrent_no_single_incident (A : Set (Site 2)) (y : Site 2)
    (p : Site 2 × Fin 2)
    (hp : p ∈ ({(y, 0), (y, 1), (y - unit 0, 0), (y - unit 1, 1)} :
      Set (Site 2 × Fin 2))) (hcross : dualCutCurrent A p ≠ 0) :
    ∃ q ∈ ({(y, 0), (y, 1), (y - unit 0, 0), (y - unit 1, 1)} :
      Set (Site 2 × Fin 2)), q ≠ p ∧ dualCutCurrent A q ≠ 0 := by
  have hsum := dualCutCurrent_divergence_zero A y
  by_contra hn
  push Not at hn
  have hvanish : ∀ q ∈ ({(y, 0), (y, 1), (y - unit 0, 0), (y - unit 1, 1)} :
      Set (Site 2 × Fin 2)), q ≠ p → dualCutCurrent A q = 0 := hn
  have hminus0 : y - unit 0 ≠ y := by
    intro h
    have := congrFun h 0
    simp [unit] at this
  have hminus1 : y - unit 1 ≠ y := by
    intro h
    have := congrFun h 1
    simp [unit] at this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp | hp
  · subst p
    have hb := hvanish (y, 1) (by simp) (by simp)
    have hc := hvanish (y - unit 0, 0) (by simp)
      (fun h => hminus0 (congrArg Prod.fst h))
    have hd := hvanish (y - unit 1, 1) (by simp) (by simp)
    omega
  · subst p
    have ha := hvanish (y, 0) (by simp) (by simp)
    have hc := hvanish (y - unit 0, 0) (by simp) (by simp)
    have hd := hvanish (y - unit 1, 1) (by simp)
      (fun h => hminus1 (congrArg Prod.fst h))
    omega
  · subst p
    have ha := hvanish (y, 0) (by simp)
      (fun h => hminus0 (congrArg Prod.fst h).symm)
    have hb := hvanish (y, 1) (by simp) (by simp)
    have hd := hvanish (y - unit 1, 1) (by simp) (by simp)
    omega
  · subst p
    have ha := hvanish (y, 0) (by simp) (by simp)
    have hb := hvanish (y, 1) (by simp)
      (fun h => hminus1 (congrArg Prod.fst h).symm)
    have hc := hvanish (y - unit 0, 0) (by simp) (by simp)
    omega

/-- The four base-named incident edges share the stated dual vertex literally. -/
theorem incident_dual_base_has_endpoint (y : Site 2) (q : Site 2 × Fin 2)
    (hq : q ∈ ({(y, 0), (y, 1), (y - unit 0, 0), (y - unit 1, 1)} :
      Set (Site 2 × Fin 2))) : y = q.1 ∨ y = q.1 + unit q.2 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (sub_add_cancel y (unit 0)).symm
  · exact Or.inr (sub_add_cancel y (unit 1)).symm

/-- Every actual past-boundary edge has a distinct literal incident continuation;
its crossing dual edge is selected unless it is exactly the outgoing exception. -/
theorem vertexPast_dual_boundary_continuation (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v y : Site 2) (p : Site 2 × Fin 2)
    (hp : p ∈ ({(y, 0), (y, 1), (y - unit 0, 0), (y - unit 1, 1)} :
      Set (Site 2 × Fin 2)))
    (hcross : dualCutCurrent (vertexPast ω hT hOne v) p ≠ 0) :
    ∃ q ∈ ({(y, 0), (y, 1), (y - unit 0, 0), (y - unit 1, 1)} :
      Set (Site 2 × Fin 2)), q ≠ p ∧
      dualCutCurrent (vertexPast ω hT hOne v) q ≠ 0 ∧
      (dualField ω (baseEdge q) = true ∨
        baseEdge (dualBase q) = outgoingEdge ω hT hOne v) := by
  obtain ⟨q, hq, hne, hc⟩ :=
    dualCutCurrent_no_single_incident (vertexPast ω hT hOne v) y p hp hcross
  refine ⟨q, hq, hne, hc, ?_⟩
  by_cases heq : baseEdge (dualBase q) = outgoingEdge ω hT hOne v
  · exact Or.inr heq
  · have hs := crossing_dual_selected ω hT hOne v (dualBase q)
      ((dualCutCurrent_ne_zero_iff _ q).mp hc) heq
    rw [dualBase_left_inv] at hs
    exact Or.inl hs

/-- Actual-past consumer: away from the endpoints of the outgoing crossing dual
edge, every boundary continuation edge is selected in the genuine dual field. -/
theorem vertexPast_dual_boundary_continues_selected (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v y : Site 2)
    (hAway0 : y ≠ (dualBaseInv (edgeEquiv.symm (outgoingEdge ω hT hOne v))).1)
    (hAway1 : y ≠ (dualBaseInv (edgeEquiv.symm (outgoingEdge ω hT hOne v))).1 +
      unit (dualBaseInv (edgeEquiv.symm (outgoingEdge ω hT hOne v))).2)
    (p : Site 2 × Fin 2)
    (hp : p ∈ ({(y, 0), (y, 1), (y - unit 0, 0), (y - unit 1, 1)} :
      Set (Site 2 × Fin 2)))
    (hcross : dualCutCurrent (vertexPast ω hT hOne v) p ≠ 0) :
    ∃ q ∈ ({(y, 0), (y, 1), (y - unit 0, 0), (y - unit 1, 1)} :
      Set (Site 2 × Fin 2)), q ≠ p ∧
      dualCutCurrent (vertexPast ω hT hOne v) q ≠ 0 ∧
      dualField ω (baseEdge q) = true := by
  obtain ⟨q, hq, hne, hc⟩ :=
    dualCutCurrent_no_single_incident (vertexPast ω hT hOne v) y p hp hcross
  refine ⟨q, hq, hne, hc, ?_⟩
  have hneOut : baseEdge (dualBase q) ≠ outgoingEdge ω hT hOne v := by
    intro heq
    have hname : dualBase q = edgeEquiv.symm (outgoingEdge ω hT hOne v) := by
      calc
        dualBase q = edgeEquiv.symm (baseEdge (dualBase q)) :=
          (edgeEquiv.symm_apply_apply _).symm
        _ = edgeEquiv.symm (outgoingEdge ω hT hOne v) := congrArg edgeEquiv.symm heq
    have hqname : q = dualBaseInv (edgeEquiv.symm (outgoingEdge ω hT hOne v)) := by
      rw [← hname, dualBase_left_inv]
    rcases incident_dual_base_has_endpoint y q hq with h | h
    · exact hAway0 (h.trans (congrArg Prod.fst hqname))
    · exact hAway1 (h.trans (congrArg (fun r : Site 2 × Fin 2 => r.1 + unit r.2) hqname))
  have hs := crossing_dual_selected ω hT hOne v (dualBase q)
    ((dualCutCurrent_ne_zero_iff _ q).mp hc) hneOut
  rw [dualBase_left_inv] at hs
  exact hs

end
end FiniteAvalanches.Trees.Lattice.PastTail
