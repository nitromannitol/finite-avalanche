import FiniteAvalanches.Trees.Lattice.PastBoundaryPath
import FiniteAvalanches.Trees.Lattice.FiniteBoundaryGeometry
import FiniteAvalanches.Trees.Lattice.PastEscapeEvent

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.PastTail
open LatticeProb SimpleGraph FiniteAvalanches.Trees.Lattice
open scoped Classical
noncomputable section

theorem vertexPast_real_boundary_escape (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v z : Site 2) (hz : z ∈ vertexPast ω hT hOne v)
    (i : Fin 2) (m : ℝ) (hfar : m < |((z i - v i : ℤ) : ℝ)|) :
    ∃ r : Site 2 × Fin 2, ((r.1 ∈ vertexPast ω hT hOne v ∧ r.1 + unit r.2 ∉ vertexPast ω hT hOne v) ∨
      (r.1 ∉ vertexPast ω hT hOne v ∧ r.1 + unit r.2 ∈ vertexPast ω hT hOne v)) ∧
      ∀ x : Site 2, (∀ j : Fin 2, |x j - v j| ≤ 1) →
        ∀ w ∈ ({(dualBaseInv r).1,
          (dualBaseInv r).1 + unit (dualBaseInv r).2} : Set (Site 2)),
          m - 1 < BarlowMasson.euclideanDistance x w := by
  let n : ℤ := |z i - v i| - 1
  have hn : n < |z i - v i| := by dsimp [n]; omega
  obtain ⟨r, _, hcross, hleft, hright⟩ :=
    BarlowMasson.finite_set_far_boundary (vertexPast ω hT hOne v)
      (vertexPast_finite ω hT hOne v) v z hz i n hn
  refine ⟨r, hcross, ?_⟩
  intro x hx w hw
  have hwfar : n < |w i - v i| := by
    rcases Set.mem_insert_iff.mp hw with h | h
    · simpa only [h] using hleft
    · simpa only [Set.mem_singleton_iff.mp h] using hright
  have htri : |w i - v i| ≤ |w i - x i| + |x i - v i| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (w i - x i) (x i - v i)
  have hcoord : |z i - v i| - 1 ≤ |w i - x i| := by
    have := hx i
    dsimp [n] at hwfar
    omega
  have hreal : |((z i - v i : ℤ) : ℝ)| - 1 ≤ |((w i - x i : ℤ) : ℝ)| := by
    exact_mod_cast hcoord
  exact lt_of_lt_of_le (by linarith only [hfar, hreal])
    (BarlowMasson.coordinate_abs_le_euclideanDistance x w i)


theorem outgoing_dual_start_near (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) (p : Site 2 × Fin 2)
    (hp : baseEdge p = outgoingEdge ω hT hOne v) :
    ∀ i : Fin 2,
      |((dualBaseInv p).1 + unit (dualBaseInv p).2) i - v i| ≤ 1 := by
  have he := congrArg Subtype.val hp
  change s(p.1, p.1 + unit p.2) = s(v, towardEnd ω hT hOne v) at he
  have hsource : p.1 = v ∨ p.1 + unit p.2 = v := by
    rcases Sym2.eq_iff.mp he with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  intro i
  have hpoint : (dualBaseInv p).1 + unit (dualBaseInv p).2 = p.1 := by
    simp only [dualBaseInv, sub_add_cancel]
  rw [hpoint]
  rcases hsource with h | h
  · rw [h]
    simp
  · have hd : p.1 i - v i = -(unit p.2 i) := by
      have hh := congrFun h i
      simp only [Pi.add_apply] at hh
      omega
    rw [hd, abs_neg]
    by_cases hi : i = p.2
    · subst i
      simp [unit]
    · simp [unit, hi]


/-- Escape of the actual past forces escape of the actual selected dual path.
All boundary/path containment is proved; no cycle premise is supplied. -/
theorem vertexPast_escape_dual_selected_path (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (hDual : IsTree (dualField ω)) (v : Site 2)
    (m : ℝ) (hm : 2 ≤ m) (hEscape : ¬vertexPast ω hT hOne v ⊆ supBall v m) :
    let d := dualBaseInv (edgeEquiv.symm (outgoingEdge ω hT hOne v))
    dualField ω ∈ BarlowMasson.treePathLeavesEuclidean (d.1 + unit d.2) d.1 (m / 2) := by
  let p := edgeEquiv.symm (outgoingEdge ω hT hOne v)
  let d := dualBaseInv p
  obtain ⟨z, hz, hfar⟩ := Set.not_subset.mp hEscape
  change ¬∀ i : Fin 2, |((z i - v i : ℤ) : ℝ)| ≤ m at hfar
  obtain ⟨i, hi⟩ := not_forall.mp hfar
  obtain ⟨r, hcross, hreach⟩ := vertexPast_real_boundary_escape ω hT hOne v z hz i m
    (lt_of_not_ge hi)
  let w := (dualBaseInv r).1
  have hw : w ∈ ({(dualBaseInv r).1,
      (dualBaseInv r).1 + unit (dualBaseInv r).2} : Set (Site 2)) := Set.mem_insert _ _
  have hp : baseEdge p = outgoingEdge ω hT hOne v := edgeEquiv.apply_symm_apply _
  have hdist := hreach (d.1 + unit d.2) (outgoing_dual_start_near ω hT hOne v p hp) w hw
  have hmem := vertexPast_boundary_endpoints_mem_selected_path ω hT hOne hDual v r hcross w hw
  refine ⟨hDual, w, hmem, ?_⟩
  change ¬BarlowMasson.euclideanDistance (d.1 + unit d.2) w ≤ m / 2
  linarith only [hm, hdist]

end
end FiniteAvalanches.Trees.Lattice.PastTail
