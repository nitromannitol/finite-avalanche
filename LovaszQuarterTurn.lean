import FiniteAvalanches.Electrical.Geometry.BSST
import Mathlib.Topology.MetricSpace.Isometry

/-! Literal coordinate transport for current source line 624.
The textbook puts primal voltage vertically and face coordinates horizontally.
The paper puts primal voltage horizontally and the negative Green field vertically.
This file proves the rigid coordinate change, without assuming a tiling conclusion. -/

namespace GeometryReview
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Source (Plane)
open Set

/-- The same clockwise quarter-turn acts on every edge square. -/
def quarterTurn (z : Plane) : Plane := (z.2, -z.1)

/-- It also preserves the maximum-coordinate metric used by the paper's analysis. -/
theorem quarterTurn_isometry : Isometry quarterTurn := by
  apply Isometry.of_dist_eq
  intro z w
  simp only [quarterTurn, Prod.dist_eq, dist_neg_neg]
  exact max_comm _ _

/-- The coordinate map preserves squared Euclidean distance, independently of
the product type's maximum-distance instance. -/
theorem quarterTurn_sq_euclidean_distance (z w : Plane) :
    ((quarterTurn z).1 - (quarterTurn w).1) ^ 2 +
      ((quarterTurn z).2 - (quarterTurn w).2) ^ 2 =
    (z.1 - w.1) ^ 2 + (z.2 - w.2) ^ 2 := by
  dsimp only [quarterTurn]
  ring

/-- Literal Euclidean distances are equal as well, not only product-metric distances. -/
theorem quarterTurn_euclidean_distance (z w : Plane) :
    Real.sqrt (((quarterTurn z).1 - (quarterTurn w).1) ^ 2 +
      ((quarterTurn z).2 - (quarterTurn w).2) ^ 2) =
    Real.sqrt ((z.1 - w.1) ^ 2 + (z.2 - w.2) ^ 2) :=
  congrArg Real.sqrt (quarterTurn_sq_euclidean_distance z w)

/-- The quarter-turn and its inverse are literal continuous coordinate maps. -/
def quarterTurnHomeomorph : Plane ≃ₜ Plane where
  toFun := quarterTurn
  invFun := fun z => (-z.2, z.1)
  left_inv := by rintro ⟨x, y⟩; simp only [quarterTurn, neg_neg]
  right_inv := by rintro ⟨x, y⟩; simp only [quarterTurn, neg_neg]
  continuous_toFun := quarterTurn_isometry.continuous
  continuous_invFun := by fun_prop

/-- Closed-square transport preserves the actual topological interior. -/
theorem quarterTurn_image_interior (Q : Set Plane) :
    quarterTurn '' interior Q = interior (quarterTurn '' Q) :=
  quarterTurnHomeomorph.image_interior Q

/-- Nonoverlap is transported in both directions; no packing premise is added. -/
theorem quarterTurn_interior_disjoint_iff (Q R : Set Plane) :
    Disjoint (interior (quarterTurn '' Q)) (interior (quarterTurn '' R)) ↔
      Disjoint (interior Q) (interior R) := by
  rw [← quarterTurn_image_interior, ← quarterTurn_image_interior]
  exact Set.disjoint_image_iff quarterTurn_isometry.injective

/-- The complete closed textbook rectangle maps to the actual copiedSquare
with the paper's negative face field, preserving each original edge ID. -/
theorem quarterTurn_image_book_square {V E W : Type} (J : CopiedGraph V E)
    (phi : V → ℝ) (G : W → ℝ) (face0 face1 : E → W) (e : E) :
    quarterTurn ''
      (Icc (min (G (face0 e)) (G (face1 e))) (max (G (face0 e)) (G (face1 e))) ×ˢ
       Icc (min (phi (J.left e)) (phi (J.right e)))
         (max (phi (J.left e)) (phi (J.right e)))) =
      copiedSquare J phi (fun F => -G F) face0 face1 e := by
  ext z
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    change y ∈ Icc _ _ ∧ -x ∈ Icc _ _
    refine ⟨hy, ?_⟩
    simpa only [mem_Icc, min_neg_neg, max_neg_neg, neg_le_neg_iff] using
      (And.intro hx.2 hx.1)
  · intro hz
    change z.1 ∈ Icc _ _ ∧ z.2 ∈ Icc _ _ at hz
    refine ⟨(-z.2, z.1), ⟨?_, hz.1⟩, ?_⟩
    · simp only [mem_Icc, min_neg_neg, max_neg_neg] at hz
      exact ⟨(le_neg.mp hz.2.2), (neg_le.mp hz.2.1)⟩
    · simp only [quarterTurn, neg_neg, Prod.mk.eta]

/-- The paper's actual negative-field copied squares have disjoint interiors
exactly when the textbook-coordinate rectangles do, for these same two IDs. -/
theorem copiedSquare_neg_field_interior_disjoint_iff {V E W : Type}
    (J : CopiedGraph V E) (phi : V → ℝ) (G : W → ℝ)
    (face0 face1 : E → W) (e f : E) :
    Disjoint (interior (copiedSquare J phi (fun F => -G F) face0 face1 e))
      (interior (copiedSquare J phi (fun F => -G F) face0 face1 f)) ↔
    Disjoint
      (interior
        (Icc (min (G (face0 e)) (G (face1 e))) (max (G (face0 e)) (G (face1 e))) ×ˢ
         Icc (min (phi (J.left e)) (phi (J.right e)))
           (max (phi (J.left e)) (phi (J.right e)))))
      (interior
        (Icc (min (G (face0 f)) (G (face1 f))) (max (G (face0 f)) (G (face1 f))) ×ˢ
         Icc (min (phi (J.left f)) (phi (J.right f)))
           (max (phi (J.left f)) (phi (J.right f))))) := by
  rw [← quarterTurn_image_book_square J phi G face0 face1 e,
    ← quarterTurn_image_book_square J phi G face0 face1 f]
  exact quarterTurn_interior_disjoint_iff _ _

/-- Source boundary square [0,p] times [-upper,-lower], including a point
when upper=lower. The whole edge family uses this same isometry. -/
theorem quarterTurn_image_boundary (upper lower : ℝ) :
    quarterTurn '' (Icc lower upper ×ˢ Icc (0 : ℝ) (upper - lower)) =
      Icc (0 : ℝ) (upper - lower) ×ˢ Icc (-upper) (-lower) := by
  ext z
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨hy, neg_le_neg hx.2, neg_le_neg hx.1⟩
  · rintro ⟨hx, hy⟩
    refine ⟨(-z.2, z.1), ⟨?_, hx⟩, ?_⟩
    · exact ⟨le_neg.mp hy.2, neg_le.mp hy.1⟩
    · simp only [quarterTurn, neg_neg, Prod.mk.eta]

/-- The omitted zero-current textbook square remains its labeled point under
the same rigid map used for positive-current copies. -/
theorem quarterTurn_image_zero_boundary (a : ℝ) :
    quarterTurn '' (Icc a a ×ˢ Icc (0 : ℝ) 0) = {(0, -a)} := by
  simpa only [sub_self, Icc_self, singleton_prod_singleton] using
    quarterTurn_image_boundary a a

/-- One actual consumer retains both a positive-current square and the
zero-current point case, using the same edge-independent isometry. -/
theorem quarterTurn_image_source_boundary_cases (a : ℝ) :
    quarterTurn '' (Icc (3 / 2 : ℝ) 2 ×ˢ Icc (0 : ℝ) (1 / 2)) =
      Icc (0 : ℝ) (1 / 2) ×ˢ Icc (-2 : ℝ) (-(3 / 2)) ∧
    quarterTurn '' (Icc a a ×ˢ Icc (0 : ℝ) 0) = {(0, -a)} := by
  constructor
  · simpa only [show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] using
      quarterTurn_image_boundary 2 (3 / 2)
  · exact quarterTurn_image_zero_boundary a

end GeometryReview

#print axioms GeometryReview.quarterTurn_isometry
#print axioms GeometryReview.quarterTurn_sq_euclidean_distance
#print axioms GeometryReview.quarterTurn_euclidean_distance
#print axioms GeometryReview.quarterTurn_image_interior
#print axioms GeometryReview.quarterTurn_interior_disjoint_iff
#print axioms GeometryReview.quarterTurn_image_book_square
#print axioms GeometryReview.copiedSquare_neg_field_interior_disjoint_iff
#print axioms GeometryReview.quarterTurn_image_boundary
#print axioms GeometryReview.quarterTurn_image_zero_boundary
#print axioms GeometryReview.quarterTurn_image_source_boundary_cases
