import FiniteAvalanches.Electrical.Green.IndicatorVariance
import FiniteAvalanches.Electrical.Green.Boundary
import FiniteAvalanches.Electrical.Trees.PathCurrent
import FiniteAvalanches.Electrical.PairContact.OrderedTreePairConsumer

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical
open scoped Classical BigOperators
noncomputable section

/-- Actual uniform tree moments on a disk boundary path give the mean-based arc bound.
The probability, Green, current, and pair identities are all proved inside this theorem. -/
theorem tree_boundary_arc_variance {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Drawing J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m + 1) → V) (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ))
    (hboundary : ∀ i t, D.curve (copies i) t ∈ circle) :
    letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
    let Y := fun T : J.SpanningTree => ∑ i : Fin m,
      J.pathIndicator T (p 0) (p (Fin.last m)) (copies i)
    let mean := (∑ T : J.SpanningTree, Y T) / (Fintype.card J.SpanningTree : ℝ)
    let G := fun i j => groundedGreen J.left J.right (p (Fin.last m)) hc (p i) (p j)
    mean = G 0 0 ∧
    (∑ T : J.SpanningTree, (Y T - mean)^2) / (Fintype.card J.SpanningTree : ℝ) ≤
      mean + 3 * ∑ i : Fin m, (G 0 i.castSucc - G 0 i.succ) *
        (G i.castSucc i.castSucc - G 0 i.castSucc + G i.succ i.succ - G 0 i.succ) := by
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  intro Y mean G
  let I := fun T : J.SpanningTree => fun i : Fin m =>
    J.pathIndicator T (p 0) (p (Fin.last m)) (copies i)
  have univ_eq (enumeration : Fintype J.SpanningTree) :
      @Finset.univ J.SpanningTree enumeration =
        @Finset.univ J.SpanningTree (Fintype.ofFinite J.SpanningTree) :=
    congrArg (fun f : Fintype J.SpanningTree => @Finset.univ J.SpanningTree f)
      (Subsingleton.elim enumeration _)
  have card_eq (enumeration : Fintype J.SpanningTree) :
      @Fintype.card J.SpanningTree enumeration =
        @Fintype.card J.SpanningTree (Fintype.ofFinite J.SpanningTree) :=
    congrArg (fun f : Fintype J.SpanningTree => @Fintype.card J.SpanningTree f)
      (Subsingleton.elim enumeration _)
  have hmean : mean = G 0 0 := by
    change (∑ T : J.SpanningTree, ∑ i : Fin m, I T i) /
      (Fintype.card J.SpanningTree : ℝ) = G 0 0
    rw [Finset.sum_comm, Finset.sum_div]
    have hI : ∀ i : Fin m, (∑ T : J.SpanningTree, I T i) /
        (Fintype.card J.SpanningTree : ℝ) = G 0 i.castSucc - G 0 i.succ :=
      by
        intro i
        have h := D.boundary_mean_pathIndicator hc hvertices hedges m p hp copies hends hboundary i
        simpa only [univ_eq, card_eq] using h
    simp_rw [hI]
    exact (groundedGreen_boundary_data J.left J.right (p (Fin.last m)) hc p rfl).1
  refine ⟨hmean, ?_⟩
  by_cases hm : m = 0
  · subst m
    have hY : ∀ T : J.SpanningTree, Y T = 0 := by
      intro T
      simp only [Y, Finset.univ_eq_empty, Finset.sum_empty]
    have hzero : mean = 0 := by simp only [mean, hY, Finset.sum_const_zero, zero_div]
    simp only [hY, hzero, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, zero_div, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero, le_refl]
  · obtain ⟨D', hreflect, θ, hmono, hspan, hangles⟩ :=
      D.boundary_path_ordered_angles m (Nat.pos_of_ne_zero hm) p hp copies hends hboundary
    have hv : ∀ x, D'.point x ∈ disk := by
      rcases hreflect with rfl | rfl
      · exact hvertices
      · exact fun x => (reflectPoint_mem_disk _).mpr (hvertices x)
    have he : ∀ e t, D'.curve e t ∈ disk := by
      rcases hreflect with rfl | rfl
      · exact hedges
      · exact fun e t => (reflectPoint_mem_disk _).mpr (hedges e t)
    obtain ⟨hcount, _hcountReal, hpair⟩ := ordered_tree_pair_contacts J D' hc hv he
      m p hp θ hmono hspan hangles copies hends
    letI : Nonempty J.SpanningTree := Fintype.card_pos_iff.mp hcount
    have hsq : ∀ T i, (I T i)^2 = I T i := by
      intro T i
      unfold I CopiedGraph.pathIndicator
      split_ifs <;> norm_num
    have hvariance := uniform_indicator_variance_eq I hsq
    have hpairs : (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then
        (∑ T : J.SpanningTree, I T i * I T j) / (Fintype.card J.SpanningTree : ℝ) else 0) =
        boundaryPairSum G := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs with hij
      · exact hpair i j hij
      · rfl
    change (∑ T : J.SpanningTree, (Y T - mean)^2) / (Fintype.card J.SpanningTree : ℝ) =
      mean + 2 * (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then
        (∑ T : J.SpanningTree, I T i * I T j) / (Fintype.card J.SpanningTree : ℝ) else 0) - mean^2
      at hvariance
    rw [hpairs] at hvariance
    have hdrop : ∀ i : Fin m, 0 ≤ G 0 i.castSucc - G 0 i.succ :=
      D.boundary_green_drop_nonneg hc hvertices hedges m p hp copies hends hboundary
    have hbound := groundedGreen_boundaryPairSum_le J.left J.right
      (p (Fin.last m)) hc p rfl hdrop
    change boundaryPairSum G ≤ (G 0 0)^2 / 2 + (3 / 2 : ℝ) * ∑ i : Fin m,
      (G 0 i.castSucc - G 0 i.succ) *
        ((G i.castSucc i.castSucc - G 0 i.castSucc) + (G i.succ i.succ - G 0 i.succ))
      at hbound
    have hgroup : (∑ i : Fin m, (G 0 i.castSucc - G 0 i.succ) *
        ((G i.castSucc i.castSucc - G 0 i.castSucc) + (G i.succ i.succ - G 0 i.succ))) =
      ∑ i : Fin m, (G 0 i.castSucc - G 0 i.succ) *
        (G i.castSucc i.castSucc - G 0 i.castSucc + G i.succ i.succ - G 0 i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hgroup, ← hmean] at hbound
    linarith only [hvariance, hbound]
end
end FiniteAvalanches.Electrical.StatementGeometry
