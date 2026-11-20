import FiniteAvalanches.Wilson.Lattice.WiredDualFaceGraph
import FiniteAvalanches.Needle.ConnectedSet
import FiniteAvalanches.Trees.Existence

/-! Connectivity of the finite square of dual faces. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Every face in the shifted square is joined to the origin by dual edges. -/
theorem wiredDualFaceGraph_reaches_origin (B : ℕ) (v : WiredDualFace B) :
    (wiredDualFaceGraph B).reaches Finset.univ v
      (wiredDualFaceOfSite B 0 (by intro i; simp)) := by
  let origin : WiredDualFace B := wiredDualFaceOfSite B 0 (by intro i; simp)
  have key : ∀ n : ℕ, ∀ v : WiredDualFace B,
      |wiredDualFaceSite v 0| + |wiredDualFaceSite v 1| ≤ n →
      (wiredDualFaceGraph B).reaches Finset.univ v origin := by
    intro n
    induction n with
    | zero =>
      intro v hn
      have hn' : |wiredDualFaceSite v 0| + |wiredDualFaceSite v 1| ≤ 0 := by exact_mod_cast hn
      have h0 : wiredDualFaceSite v 0 = 0 :=
        abs_eq_zero.mp (le_antisymm (by linarith [abs_nonneg (wiredDualFaceSite v 1)]) (abs_nonneg _))
      have h1 : wiredDualFaceSite v 1 = 0 :=
        abs_eq_zero.mp (le_antisymm (by linarith [abs_nonneg (wiredDualFaceSite v 0)]) (abs_nonneg _))
      have hv : v = origin := by
        apply wiredDualFaceSite_injective B
        funext i
        fin_cases i
        · exact h0
        · exact h1
      rw [hv]
      exact .refl
    | succ n ih =>
      intro v hn
      let x := wiredDualFaceSite v
      have hn' : |x 0| + |x 1| ≤ (n : ℤ) + 1 := by exact_mod_cast hn
      by_cases hx : x = 0
      · have hv : v = origin := wiredDualFaceSite_injective B hx
        rw [hv]
        exact .refl
      have hi : ∃ i : Fin 2, x i ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (funext h)
      obtain ⟨i, hi⟩ := hi
      obtain ⟨y, hadj, hyi, hyj⟩ := FiniteAvalanches.Needle.exists_axis_step x i hi
      have hy : inDualFaceBox B y := by
        intro j
        by_cases hji : j = i
        · subst j
          have hv := (v i).property
          change -(B : ℤ) - 1 ≤ x i ∧ x i ≤ B at hv
          have habs : |x i| ≤ (B : ℤ) + 1 := by rw [abs_le]; omega
          have hyabs : |y i| ≤ (B : ℤ) := by omega
          have hybounds := (abs_le.mp hyabs)
          omega
        · rw [hyj j hji]
          exact (v j).property
      let w := wiredDualFaceOfSite B y hy
      have hadj' : (wiredDualFaceGraph B).adjacent Finset.univ v w := by
        apply (wiredDualFaceGraph_adjacent_iff B v w).mpr
        exact hadj
      have hsum : |y 0| + |y 1| ≤ (n : ℤ) := by
        fin_cases i
        · change |y 0| + 1 = |x 0| at hyi
          have h := hyj 1 (by decide)
          rw [h]
          omega
        · change |y 1| + 1 = |x 1| at hyi
          have h := hyj 0 (by decide)
          rw [h]
          omega
      have hsum' : |wiredDualFaceSite w 0| + |wiredDualFaceSite w 1| ≤ n := by
        change |y 0| + |y 1| ≤ (n : ℤ)
        exact hsum
      exact Relation.ReflTransGen.head hadj' (ih w hsum')
  have hnn : (0 : ℤ) ≤ |wiredDualFaceSite v 0| + |wiredDualFaceSite v 1| := by positivity
  exact key (|wiredDualFaceSite v 0| + |wiredDualFaceSite v 1|).toNat v
    (le_of_eq (Int.toNat_of_nonneg hnn).symm)

/-- Every two faces of the shifted square are connected by its dual edges. -/
theorem wiredDualFaceGraph_connected (B : ℕ) (v w : WiredDualFace B) :
    (wiredDualFaceGraph B).reaches Finset.univ v w :=
  (wiredDualFaceGraph_reaches_origin B v).trans
    ((wiredDualFaceGraph B).reaches_symm (wiredDualFaceGraph_reaches_origin B w))

/-- The finite dual face graph has a spanning tree. -/
instance wiredDualFaceGraph_spanningTree_nonempty (B : ℕ) :
    Nonempty (wiredDualFaceGraph B).SpanningTree := by
  letI : Nonempty (WiredDualFace B) :=
    ⟨wiredDualFaceOfSite B 0 (by intro i; simp)⟩
  exact (wiredDualFaceGraph B).nonempty_spanning_tree (wiredDualFaceGraph_connected B)

end
end FiniteAvalanches.Wilson.Lattice
