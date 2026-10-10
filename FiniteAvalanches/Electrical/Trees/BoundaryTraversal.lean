import FiniteAvalanches.Electrical.Trees.SignedPathTraversal
import FiniteAvalanches.Electrical.Geometry.BoundaryReflection
import FiniteAvalanches.Electrical.Geometry.BoundaryPathOrder

namespace FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical BigOperators
noncomputable section
namespace CopiedGraph
variable {V E : Type} [Fintype V] [Fintype E]
omit [Fintype V] [Fintype E] in
/-- The signed observable is exactly the difference of the two oriented path indicators. -/
theorem signedPathTraversal_eq_difference (J : CopiedGraph V E) (T : J.SpanningTree)
    (u v : V) (e : E) :
    J.signedPathTraversal T u v e =
      (if e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v ∧
        J.reaches (T.val.erase e) u (J.left e) then (1 : ℝ) else 0) -
      (if e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v ∧
        J.reaches (T.val.erase e) u (J.right e) then (1 : ℝ) else 0) := by
  by_cases hhit : e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v
  · have hlr : ¬(J.reaches (T.val.erase e) u (J.left e) ∧
        J.reaches (T.val.erase e) u (J.right e)) := by
      intro h
      have hp := J.separating_pairings T e hhit.1 u v hhit.2
      rcases hp with ⟨_,hrv⟩ | ⟨_,hlv⟩
      · exact hhit.2 (h.2.trans hrv)
      · exact hhit.2 (h.1.trans hlv)
    have hor : J.reaches (T.val.erase e) u (J.left e) ∨
        J.reaches (T.val.erase e) u (J.right e) :=
      (J.separating_pairings T e hhit.1 u v hhit.2).imp And.left And.left
    rcases hor with hl | hr
    · have hn : ¬J.reaches (T.val.erase e) u (J.right e) := fun hr => hlr ⟨hl,hr⟩
      simp [signedPathTraversal, hhit.1, hhit.2, hl, hn]
    · have hn : ¬J.reaches (T.val.erase e) u (J.left e) := fun hl => hlr ⟨hl,hr⟩
      simp [signedPathTraversal, hhit.1, hhit.2, hr, hn]
  · have hfalse (P : Prop) : ¬(e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v ∧ P) :=
      fun h => hhit ⟨h.1,h.2.1⟩
    simp only [signedPathTraversal, if_neg hhit, if_neg (hfalse _), sub_self]

end CopiedGraph

namespace Drawing
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Every contacted boundary copy is traversed forwards along the actual boundary path.
One reflection is used only to apply circle separation; stored copied IDs never change. -/
theorem boundary_signedPathTraversal (D : Drawing J) (T : J.SpanningTree)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m + 1) → V) (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ))
    (hboundary : ∀ i t, D.curve (copies i) t ∈ circle) (i : Fin m) :
    J.signedPathTraversal T (p 0) (p (Fin.last m)) (copies i) =
      (if J.left (copies i) = p i.castSucc then (1 : ℝ) else -1) *
        J.pathIndicator T (p 0) (p (Fin.last m)) (copies i) := by
  by_cases hhit : copies i ∈ T.val ∧
      ¬J.reaches (T.val.erase (copies i)) (p 0) (p (Fin.last m))
  · obtain ⟨D', hD, θ, hθ, hspan, hpoint⟩ :=
      D.boundary_path_ordered_angles m (by have := i.isLt; omega) p hp copies hends hboundary
    have hv : ∀ x, D'.point x ∈ disk := by
      rcases hD with rfl | rfl
      · exact hvertices
      · exact fun x => (reflectPoint_mem_disk _).mpr (hvertices x)
    have he : ∀ e t, D'.curve e t ∈ disk := by
      rcases hD with rfl | rfl
      · exact hedges
      · exact fun e t => (reflectPoint_mem_disk _).mpr (hedges e t)
    have hforward := D'.boundary_copy_forward T hv he m p θ hθ hspan hpoint
      i (copies i) (hends i) hhit.1 hhit.2
    have hne : p i.succ ≠ p i.castSucc := by
      intro h
      have := congrArg Fin.val (hp h)
      simp only [Fin.val_succ, Fin.val_castSucc] at this
      omega
    rcases hends i with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · have hreach : J.reaches (T.val.erase (copies i)) (p 0) (J.left (copies i)) :=
        by simpa only [hl] using hforward.1
      rw [CopiedGraph.signedPathTraversal, if_pos hhit, if_pos hreach,
        CopiedGraph.pathIndicator, if_pos hhit]
      simp only [hl, ↓reduceIte, mul_one]
    · have hnot : ¬J.reaches (T.val.erase (copies i)) (p 0) (J.left (copies i)) := by
        rw [hl]
        exact fun h => hhit.2 (h.trans hforward.2)
      rw [CopiedGraph.signedPathTraversal, if_pos hhit, if_neg hnot,
        CopiedGraph.pathIndicator, if_pos hhit]
      simp only [hl, if_neg hne, mul_one]
  · simp [CopiedGraph.signedPathTraversal, CopiedGraph.pathIndicator, hhit]

/-- Reorient the signed tree traversal before averaging on the full original tree carrier. -/
theorem boundary_pathIndicator_average_eq (D : Drawing J)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m + 1) → V) (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ))
    (hboundary : ∀ i t, D.curve (copies i) t ∈ circle) (i : Fin m) :
    (∑ T : J.SpanningTree, J.pathIndicator T (p 0) (p (Fin.last m)) (copies i)) /
      (Fintype.card J.SpanningTree : ℝ) =
    (if J.left (copies i) = p i.castSucc then (1 : ℝ) else -1) *
      ((∑ T : J.SpanningTree,
        J.signedPathTraversal T (p 0) (p (Fin.last m)) (copies i)) /
        (Fintype.card J.SpanningTree : ℝ)) := by
  have hsum : (∑ T : J.SpanningTree,
      J.signedPathTraversal T (p 0) (p (Fin.last m)) (copies i)) =
      (if J.left (copies i) = p i.castSucc then (1 : ℝ) else -1) *
        (∑ T : J.SpanningTree, J.pathIndicator T (p 0) (p (Fin.last m)) (copies i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ =>
      D.boundary_signedPathTraversal T hvertices hedges m p hp copies hends hboundary i
  rw [hsum]
  split_ifs <;> ring

/-- The source boundary mean is exactly the classical stored-current specialization.
This equivalence does not assume either mean identity. -/
theorem boundary_first_moment_iff (D : Drawing J)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m + 1) → V) (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ))
    (hboundary : ∀ i t, D.curve (copies i) t ∈ circle)
    (hc : (FiniteAvalanches.Electrical.supportGraph J.left J.right).Preconnected)
    (i : Fin m) :
    ((∑ T : J.SpanningTree, J.pathIndicator T (p 0) (p (Fin.last m)) (copies i)) /
      (Fintype.card J.SpanningTree : ℝ) =
      FiniteAvalanches.Electrical.groundedGreen J.left J.right (p (Fin.last m)) hc (p 0)
        (p i.castSucc) -
      FiniteAvalanches.Electrical.groundedGreen J.left J.right (p (Fin.last m)) hc (p 0)
        (p i.succ)) ↔
    ((∑ T : J.SpanningTree, J.signedPathTraversal T (p 0) (p (Fin.last m)) (copies i)) /
      (Fintype.card J.SpanningTree : ℝ) =
      FiniteAvalanches.Electrical.groundedGreen J.left J.right (p (Fin.last m)) hc (p 0)
        (J.left (copies i)) -
      FiniteAvalanches.Electrical.groundedGreen J.left J.right (p (Fin.last m)) hc (p 0)
        (J.right (copies i))) := by
  have haverage := D.boundary_pathIndicator_average_eq hvertices hedges m p hp copies hends hboundary i
  have hcurrent := J.stored_current_reorient
    (FiniteAvalanches.Electrical.groundedGreen J.left J.right (p (Fin.last m)) hc (p 0))
    (copies i) (p i.castSucc) (p i.succ) (hends i)
  rw [haverage, ← hcurrent]
  split_ifs <;> constructor <;> intro h <;> linarith

end Drawing
end
end FiniteAvalanches.Electrical.StatementGeometry
