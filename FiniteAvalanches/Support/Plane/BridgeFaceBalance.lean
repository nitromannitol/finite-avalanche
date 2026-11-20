import FiniteAvalanches.Support.Plane.PolarDualConnected
import FiniteAvalanches.Support.Plane.BoundaryIncidenceCount

/-!
# Face-boundary balance at bridge-only vertices

A bridge has the same dual face on both sides. Hence the face boundary of a
vertex-indicator gradient vanishes at any vertex incident only to bridges.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Plane Set
open scoped Classical BigOperators

variable {V E : Type} [Fintype V] [Fintype E]

/-- The two chart sides of a bridge represent the same complementary face. -/
theorem chartFaces_eq_of_bridge {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) (e : E)
    (hbridge : ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) :
    negativeChartFace D e (charts e) = positiveChartFace D e (charts e) := by
  classical
  letI : Nonempty E := ⟨e⟩
  have h := not_not.mp (mt (edge_path_duality D charts (Finset.univ.erase e) e
    (Finset.notMem_erase _ _)).mpr hbridge)
  have hs : (Finset.univ.erase e)ᶜ.erase e = (∅ : Finset E) := by
    ext f
    simp
  rw [hs] at h
  exact CopiedGraph.eq_of_reaches_empty _ h

/-- At a vertex incident only to bridges, every face has zero boundary of the
vertex-indicator gradient. -/
theorem indicator_face_boundary_eq_zero_of_incident_bridges {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e) (v : V)
    (hbridge : ∀ e : E, (J.left e = v ∨ J.right e = v) →
      ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e))
      (copyGradient J.left J.right (Pi.single v 1)) F = 0 := by
  classical
  unfold copyBoundary
  apply Finset.sum_eq_zero
  intro e _
  dsimp only
  by_cases he : J.left e = v ∨ J.right e = v
  · have heq := chartFaces_eq_of_bridge D charts e (hbridge e he)
    by_cases hn : negativeChartFace D e (charts e) = F
    · have hp : positiveChartFace D e (charts e) = F := heq.symm.trans hn
      simp only [hn, hp, if_true, sub_self]
    · have hp : positiveChartFace D e (charts e) ≠ F := fun h => hn (heq.trans h)
      simp only [hn, hp, if_false, sub_self]
  · have hl : v ≠ J.left e := fun h => he (Or.inl h.symm)
    have hr : v ≠ J.right e := fun h => he (Or.inr h.symm)
    simp [copyGradient, hl, hr]

end FiniteAvalanches.Electrical.StatementGeometry
