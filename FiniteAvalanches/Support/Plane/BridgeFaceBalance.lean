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

/-- An edge is a bridge exactly when its two chart sides are in the same face. -/
theorem bridge_iff_chartFaces_eq {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) (e : E) :
    (¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) ↔
      negativeChartFace D e (charts e) = positiveChartFace D e (charts e) := by
  classical
  constructor
  · exact chartFaces_eq_of_bridge D charts e
  · intro hface hreach
    letI : Nonempty E := ⟨e⟩
    have hnot := (edge_path_duality D charts (Finset.univ.erase e) e
      (Finset.notMem_erase _ _)).mp hreach
    apply hnot
    rw [hface]
    exact .refl

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

/-- The dual boundary of every primal gradient vanishes in a forest drawing. -/
theorem face_boundary_gradient_eq_zero_of_forest {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e)
    (hforest : ∀ e : E, ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e))
    (q : V → ℝ) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e)) (copyGradient J.left J.right q) F = 0 := by
  apply ((copyBoundary_gradient_eq_zero_iff_indicators J.left J.right
    (fun e => negativeChartFace D e (charts e))
    (fun e => positiveChartFace D e (charts e))).mpr ?_) q F
  intro v G
  exact indicator_face_boundary_eq_zero_of_incident_bridges D charts v (fun e _ => hforest e) G


/-- For a vertex indicator, only incident non-loop edges whose chart sides
are distinct contribute to the dual boundary. -/
theorem indicator_face_boundary_eq_sum_relevant_edges {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e) (v : V) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e))
      (copyGradient J.left J.right (Pi.single v 1)) F =
    ∑ e ∈ Finset.univ.filter (fun e => (J.left e = v ∨ J.right e = v) ∧
        J.left e ≠ J.right e ∧
        J.reaches (Finset.univ.erase e) (J.left e) (J.right e)),
      ((if negativeChartFace D e (charts e) = F then
          copyGradient J.left J.right (Pi.single v 1) e else 0) -
       (if positiveChartFace D e (charts e) = F then
          copyGradient J.left J.right (Pi.single v 1) e else 0)) := by
  classical
  unfold copyBoundary
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e _ he
  have hn : ¬ ((J.left e = v ∨ J.right e = v) ∧
      J.left e ≠ J.right e ∧
      J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he
  by_cases hi : J.left e = v ∨ J.right e = v
  · by_cases hl : J.left e = J.right e
    · simp only [copyGradient, hl, sub_self, ite_self]
    · have hb : ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e) :=
        fun h => hn ⟨hi, hl, h⟩
      have hf := chartFaces_eq_of_bridge D charts e hb
      rw [hf, sub_self]
  · have hl : v ≠ J.left e := fun h => hi (Or.inl h.symm)
    have hr : v ≠ J.right e := fun h => hi (Or.inr h.symm)
    simp [copyGradient, hl, hr]


/-- A vertex has zero indicator boundary when every incident non-loop edge
is a bridge; loops may be present. -/
theorem indicator_face_boundary_eq_zero_of_incident_nonloop_bridges {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e) (v : V)
    (hbridge : ∀ e : E, (J.left e = v ∨ J.right e = v) →
      J.left e ≠ J.right e →
      ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e))
      (copyGradient J.left J.right (Pi.single v 1)) F = 0 := by
  classical
  rw [indicator_face_boundary_eq_sum_relevant_edges]
  apply Finset.sum_eq_zero
  intro e he
  have he' := (Finset.mem_filter.mp he).2
  exact (hbridge e he'.1 he'.2.1 he'.2.2).elim

/-- The dual boundary of every gradient vanishes when all non-loop edges are
bridges, with arbitrary loop copies allowed. -/
theorem face_boundary_gradient_eq_zero_of_nonloop_bridges {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e)
    (hbridge : ∀ e : E, J.left e ≠ J.right e →
      ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e))
    (q : V → ℝ) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e)) (copyGradient J.left J.right q) F = 0 := by
  apply ((copyBoundary_gradient_eq_zero_iff_indicators J.left J.right
    (fun e => negativeChartFace D e (charts e))
    (fun e => positiveChartFace D e (charts e))).mpr ?_) q F
  intro v G
  exact indicator_face_boundary_eq_zero_of_incident_nonloop_bridges D charts v
    (fun e _ => hbridge e) G

end FiniteAvalanches.Electrical.StatementGeometry
