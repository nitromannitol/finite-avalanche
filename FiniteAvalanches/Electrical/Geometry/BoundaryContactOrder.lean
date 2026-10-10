import FiniteAvalanches.Electrical.Geometry.BoundaryReflection
import FiniteAvalanches.Electrical.Geometry.BoundaryPathOrder

namespace FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical
noncomputable section
namespace Drawing
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Boundary contact directions and order follow from the literal proper disk drawing.
Adjacent indices and the two path endpoints are included; every original copied ID is retained. -/
theorem boundary_contacts_ordered (D : Drawing J) (T : J.SpanningTree)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m + 1) → V) (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ))
    (hboundary : ∀ i t, D.curve (copies i) t ∈ circle)
    (i j : Fin m) (hij : i < j) (hi : copies i ∈ T.val) (hj : copies j ∈ T.val)
    (hci : ¬J.reaches (T.val.erase (copies i)) (p 0) (p (Fin.last m)))
    (hcj : ¬J.reaches (T.val.erase (copies j)) (p 0) (p (Fin.last m))) :
    (J.reaches (T.val.erase (copies i)) (p 0) (p i.castSucc) ∧
      J.reaches (T.val.erase (copies i)) (p i.succ) (p (Fin.last m))) ∧
    (J.reaches (T.val.erase (copies j)) (p 0) (p j.castSucc) ∧
      J.reaches (T.val.erase (copies j)) (p j.succ) (p (Fin.last m))) ∧
    ¬J.reaches (T.val.erase (copies i)) (p 0) (p j.castSucc) := by
  obtain ⟨D', hD, θ, hθ, hspan, hpoint⟩ :=
    D.boundary_path_ordered_angles m (by omega) p hp copies hends hboundary
  have hv : ∀ x, D'.point x ∈ disk := by
    rcases hD with rfl | rfl
    · exact hvertices
    · exact fun x => (reflectPoint_mem_disk _).mpr (hvertices x)
  have he : ∀ e t, D'.curve e t ∈ disk := by
    rcases hD with rfl | rfl
    · exact hedges
    · exact fun e t => (reflectPoint_mem_disk _).mpr (hedges e t)
  refine ⟨D'.boundary_copy_forward T hv he m p θ hθ hspan hpoint i (copies i) (hends i) hi hci,
    D'.boundary_copy_forward T hv he m p θ hθ hspan hpoint j (copies j) (hends j) hj hcj, ?_⟩
  exact D'.boundary_copies_increasing T hv he m p θ hθ hspan hpoint i j hij
    (copies i) (copies j) ((D.simple_path_copies_injective m p hp copies hends).ne hij.ne)
    (hends i) (hends j) hi hj hci

end Drawing
end
end FiniteAvalanches.Electrical.StatementGeometry
