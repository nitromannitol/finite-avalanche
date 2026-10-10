import FiniteAvalanches.Trees.Lattice.BoundaryContinuation
import FiniteAvalanches.Trees.Lattice.PastBond

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.PastTail
open LatticeProb SimpleGraph
open scoped Classical BigOperators
noncomputable section

/-- Antisymmetric flux on actual dual lattice vertices, retaining each once-named
original dual edge. The four unit directions are summed without selecting edges. -/
def latticeCutFlux (A : Set (Site 2)) (x y : Site 2) : ℤ :=
  ∑ i : Fin 2, ((if y = x + unit i then dualCutCurrent A (x, i) else 0) -
    (if x = y + unit i then dualCutCurrent A (y, i) else 0))

theorem latticeCutFlux_antisymmetric (A : Set (Site 2)) (x y : Site 2) :
    latticeCutFlux A x y = -latticeCutFlux A y x := by
  unfold latticeCutFlux
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  omega

theorem dualCutCurrent_finite_support (A : Set (Site 2)) (hA : A.Finite) :
    {p : Site 2 × Fin 2 | dualCutCurrent A p ≠ 0}.Finite := by
  apply (Set.Finite.preimage
    (Set.injOn_of_injective (baseEdge_injective.comp dualBaseEquiv.injective))
    (latticeBoundary_finite A hA)).subset
  intro p hp
  apply (mem_latticeBoundary_iff A (dualBase p).1
    ((dualBase p).1 + unit (dualBase p).2) ⟨(dualBase p).2, Or.inl rfl⟩).mpr
  rcases (dualCutCurrent_ne_zero_iff A p).mp hp with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.2, h.1⟩

/-- A nonzero flux coefficient names a genuine crossed original edge, in one of
its two orientations. There is no quotient or aggregation of distinct edge IDs. -/
theorem latticeCutFlux_ne_zero_edge (A : Set (Site 2)) (x y : Site 2)
    (hf : latticeCutFlux A x y ≠ 0) :
    ∃ p : Site 2 × Fin 2, dualCutCurrent A p ≠ 0 ∧
      ((x = p.1 ∧ y = p.1 + unit p.2) ∨ (y = p.1 ∧ x = p.1 + unit p.2)) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hf
  by_cases hplus : y = x + unit i
  · by_cases hj : dualCutCurrent A (x, i) = 0
    · have hpos : (if y = x + unit i then dualCutCurrent A (x, i) else 0) = 0 := by
        rw [if_pos hplus, hj]
      have hminus : x = y + unit i := by
        by_contra hn
        exact hi (by rw [hpos, if_neg hn]; omega)
      have hne : dualCutCurrent A (y, i) ≠ 0 := by
        intro hzero
        exact hi (by rw [hpos, if_pos hminus, hzero]; omega)
      exact ⟨(y, i), hne, Or.inr ⟨rfl, hminus⟩⟩
    · exact ⟨(x, i), hj, Or.inl ⟨rfl, hplus⟩⟩
  · have hminus : x = y + unit i := by
      by_contra hn
      exact hi (by rw [if_neg hplus, if_neg hn]; omega)
    have hne : dualCutCurrent A (y, i) ≠ 0 := by
      intro hzero
      exact hi (by rw [if_neg hplus, if_pos hminus, hzero]; omega)
    exact ⟨(y, i), hne, Or.inr ⟨rfl, hminus⟩⟩

theorem latticeCutFlux_finite_support (A : Set (Site 2)) (hA : A.Finite) :
    {r : Site 2 × Site 2 | latticeCutFlux A r.1 r.2 ≠ 0}.Finite := by
  let S : Set (Site 2 × Fin 2) := {p | dualCutCurrent A p ≠ 0}
  have hS : S.Finite := dualCutCurrent_finite_support A hA
  apply ((hS.image (fun p => (p.1, p.1 + unit p.2))).union
    (hS.image (fun p => (p.1 + unit p.2, p.1)))).subset
  rintro ⟨x, y⟩ hf
  obtain ⟨p, hp, h | h⟩ := latticeCutFlux_ne_zero_edge A x y hf
  · exact Or.inl ⟨p, hp, Prod.ext h.1.symm h.2.symm⟩
  · exact Or.inr ⟨p, hp, Prod.ext h.2.symm h.1.symm⟩

private theorem plus_unit_injective (x : Site 2) : Function.Injective (fun i : Fin 2 => x + unit i) := by
  intro i j h
  have hu := congrFun (add_left_cancel h) i
  fin_cases i <;> fin_cases j <;> simp [unit] at hu ⊢

private theorem no_two_positive_steps (x : Site 2) (i j : Fin 2) :
    x ≠ x + unit i + unit j := by
  intro h
  have he := congrFun h i
  fin_cases i <;> fin_cases j <;> simp [unit] at he <;> omega

theorem latticeCutFlux_base (A : Set (Site 2)) (x : Site 2) (i : Fin 2) :
    latticeCutFlux A x (x + unit i) = dualCutCurrent A (x, i) := by
  unfold latticeCutFlux
  rw [Finset.sum_sub_distrib]
  have hpos : (∑ j : Fin 2, if x + unit i = x + unit j then dualCutCurrent A (x, j) else 0) =
      dualCutCurrent A (x, i) := by
    simp only [(plus_unit_injective x).eq_iff]
    simp
  have hneg : (∑ j : Fin 2, if x = x + unit i + unit j then
      dualCutCurrent A (x + unit i, j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact if_neg (no_two_positive_steps x i j)
  rw [hpos, hneg, sub_zero]

/-- The finite vertex window is only a carrier for a finite sum; once it contains
both endpoints of every nonzero coefficient, the actual lattice divergence is zero. -/
theorem latticeCutFlux_divergence_zero (A : Set (Site 2)) (W : Finset (Site 2))
    (hW : ∀ x y, latticeCutFlux A x y ≠ 0 → x ∈ W ∧ y ∈ W) (x : Site 2) :
    ∑ y ∈ W, latticeCutFlux A x y = 0 := by
  unfold latticeCutFlux
  rw [Finset.sum_comm]
  have hpos : ∀ i : Fin 2,
      (∑ y ∈ W, if y = x + unit i then dualCutCurrent A (x, i) else 0) =
        dualCutCurrent A (x, i) := by
    intro i
    by_cases hi : dualCutCurrent A (x, i) = 0
    · simp only [hi, ite_self, Finset.sum_const_zero]
    · have hx : x + unit i ∈ W := (hW x (x + unit i) (by rwa [latticeCutFlux_base])).2
      rw [Finset.sum_eq_single_of_mem (x + unit i) hx]
      · exact if_pos rfl
      · intro y _ hy; exact if_neg hy
  have hneg : ∀ i : Fin 2,
      (∑ y ∈ W, if x = y + unit i then dualCutCurrent A (y, i) else 0) =
        dualCutCurrent A (x - unit i, i) := by
    intro i
    have hiff : ∀ y : Site 2, x = y + unit i ↔ y = x - unit i := by
      intro y
      constructor
      · intro h; rw [h, add_sub_cancel_right]
      · rintro rfl; exact (sub_add_cancel x (unit i)).symm
    simp only [hiff]
    by_cases hi : dualCutCurrent A (x - unit i, i) = 0
    · rw [hi]
      apply Finset.sum_eq_zero
      intro y _
      split_ifs with hy
      · simpa only [hy] using hi
      · rfl
    · have hflux : latticeCutFlux A (x - unit i) x ≠ 0 := by
        simpa only [← latticeCutFlux_base A (x - unit i) i, sub_add_cancel] using hi
      have hx : x - unit i ∈ W := (hW _ _ hflux).1
      rw [Finset.sum_eq_single_of_mem (x - unit i) hx]
      · simp only [ite_true]
      · intro y _ hy; exact if_neg hy
  simp_rw [Finset.sum_sub_distrib, hpos, hneg]
  simp only [Fin.sum_univ_two]
  have h := dualCutCurrent_divergence_zero A x
  omega

end
end FiniteAvalanches.Trees.Lattice.PastTail
