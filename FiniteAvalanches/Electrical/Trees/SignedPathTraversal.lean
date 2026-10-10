import FiniteAvalanches.Electrical.Geometry.DiskDrawing
import FiniteAvalanches.Electrical.Trees.GroveNoncrossing

namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- Signed traversal of an original copy on the unique source-to-ground tree path.
The sign is positive in the stored left-to-right direction. -/
def signedPathTraversal (J : CopiedGraph V E) (T : J.SpanningTree)
    (u v : V) (e : E) : ℝ :=
  if e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v then
    if J.reaches (T.val.erase e) u (J.left e) then 1 else -1
  else 0

omit [Fintype V] [Fintype E] in
theorem signedPathTraversal_self (J : CopiedGraph V E) (T : J.SpanningTree)
    (u : V) (e : E) : J.signedPathTraversal T u u e = 0 := by
  simp only [signedPathTraversal, not_true_eq_false, and_false, ↓reduceIte,
    show J.reaches (T.val.erase e) u u from .refl]

omit [Fintype V] [Fintype E] in
theorem signedPathTraversal_loop (J : CopiedGraph V E) (T : J.SpanningTree)
    (u v : V) (e : E) (he : J.left e = J.right e) :
    J.signedPathTraversal T u v e = 0 := by
  simp [signedPathTraversal, J.loop_not_mem T e he]

omit [Fintype V] [Fintype E] in
theorem abs_signedPathTraversal (J : CopiedGraph V E) (T : J.SpanningTree)
    (u v : V) (e : E) :
    |J.signedPathTraversal T u v e| = J.pathIndicator T u v e := by
  unfold signedPathTraversal pathIndicator
  split_ifs <;> norm_num

omit [Fintype V] [Fintype E] in
/-- The source component determines the orientation, without choosing a path. -/
theorem signedPathTraversal_eq_of_separates (J : CopiedGraph V E)
    (T : J.SpanningTree) (u v : V) (e : E) (he : e ∈ T.val)
    (hsep : ¬J.reaches (T.val.erase e) u v)
    (hl : J.reaches (T.val.erase e) u (J.left e)) :
    J.signedPathTraversal T u v e = 1 := by
  simp [signedPathTraversal, he, hsep, hl]

omit [Fintype V] [Fintype E] in
/-- Reversing storage reverses the current sign, including zero current and loops. -/
theorem stored_current_reorient (J : CopiedGraph V E) (f : V → ℝ)
    (e : E) (x y : V)
    (hends : (J.left e = x ∧ J.right e = y) ∨
      (J.right e = x ∧ J.left e = y)) :
    (if J.left e = x then (1 : ℝ) else -1) *
      (f (J.left e) - f (J.right e)) = f x - f y := by
  rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · simp [hl, hr]
  · by_cases hxy : y = x
    · simp [hl, hr, hxy]
    · simp [hl, hr, hxy]

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph

namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical BigOperators
open FiniteAvalanches.Electrical
variable {V E : Type} [Fintype V] [Fintype E]

/-- Equal terminals give zero mean and zero electrical current, without a classical input. -/
theorem mean_signedPathTraversal_self (J : CopiedGraph V E) (v : V)
    (hc : (supportGraph J.left J.right).Preconnected) (e : E) :
    (∑ T : J.SpanningTree, J.signedPathTraversal T v v e) /
      (Fintype.card J.SpanningTree : ℝ) =
      groundedGreen J.left J.right v hc v (J.left e) -
        groundedGreen J.left J.right v hc v (J.right e) := by
  simp [signedPathTraversal_self, groundedGreen_ground_source]

end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
