import FiniteAvalanches.Electrical.Trees.BoundaryTraversal
import FiniteAvalanches.External.KirchhoffTreePathCurrent

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.Drawing
open FiniteAvalanches.Electrical
open scoped Classical BigOperators
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Boundary contact probabilities are the actual nonnegative consecutive Green drops. -/
theorem boundary_mean_pathIndicator (D : Drawing J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m + 1) → V) (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ))
    (hboundary : ∀ i t, D.curve (copies i) t ∈ circle) (i : Fin m) :
    (∑ T : J.SpanningTree, J.pathIndicator T (p 0) (p (Fin.last m)) (copies i)) /
      (Fintype.card J.SpanningTree : ℝ) =
      groundedGreen J.left J.right (p (Fin.last m)) hc (p 0) (p i.castSucc) -
      groundedGreen J.left J.right (p (Fin.last m)) hc (p 0) (p i.succ) := by
  apply (D.boundary_first_moment_iff hvertices hedges m p hp copies hends hboundary hc i).mpr
  apply FiniteAvalanches.External.kirchhoff_meanTreePathCurrent J (p (Fin.last m)) hc
    (p 0) _ (copies i)
  intro h
  have he := congrArg Fin.val (hp h)
  simp only [Fin.val_zero, Fin.val_last] at he
  have hi := i.isLt
  omega

/-- Positivity is derived from the uniform indicator law; zero probabilities are retained. -/
theorem boundary_green_drop_nonneg (D : Drawing J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m + 1) → V) (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ))
    (hboundary : ∀ i t, D.curve (copies i) t ∈ circle) (i : Fin m) :
    0 ≤ groundedGreen J.left J.right (p (Fin.last m)) hc (p 0) (p i.castSucc) -
      groundedGreen J.left J.right (p (Fin.last m)) hc (p 0) (p i.succ) := by
  rw [← D.boundary_mean_pathIndicator hc hvertices hedges m p hp copies hends hboundary i]
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro T _
  unfold CopiedGraph.pathIndicator
  split_ifs <;> norm_num
end FiniteAvalanches.Electrical.StatementGeometry.Drawing
