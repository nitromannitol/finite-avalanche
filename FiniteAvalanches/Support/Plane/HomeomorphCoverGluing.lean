import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Homeomorph.Defs

/-!
# Gluing homeomorphisms along finite closed covers

Homeomorphisms that carry the pieces of a finite closed cover onto the pieces
of a second finite closed cover, and that agree on overlaps together with their
inverses, glue to a single homeomorphism.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]

/-- The homeomorphism glued from piecewise homeomorphisms on finite closed covers. -/
noncomputable def homeomorphOfClosedCover (S : ι → Set X) (T : ι → Set Y)
    (hS : ∀ i, IsClosed (S i)) (hT : ∀ i, IsClosed (T i))
    (hScov : ∀ x, ∃ i, x ∈ S i) (hTcov : ∀ y, ∃ i, y ∈ T i)
    (h : ι → X ≃ₜ Y) (himage : ∀ i, h i '' S i = T i)
    (hagree : ∀ i j x, x ∈ S i → x ∈ S j → h i x = h j x)
    (hagree' : ∀ i j y, y ∈ T i → y ∈ T j → (h i).symm y = (h j).symm y) : X ≃ₜ Y where
  toFun x := h (Classical.choose (hScov x)) x
  invFun y := (h (Classical.choose (hTcov y))).symm y
  left_inv x := by
    have hi : x ∈ S (Classical.choose (hScov x)) := Classical.choose_spec (hScov x)
    have hy : h (Classical.choose (hScov x)) x ∈ T (Classical.choose (hScov x)) := by
      rw [← himage]
      exact mem_image_of_mem _ hi
    have hj := Classical.choose_spec (hTcov (h (Classical.choose (hScov x)) x))
    change (h (Classical.choose (hTcov _))).symm _ = x
    rw [hagree' _ _ _ hj hy]
    exact (h _).symm_apply_apply x
  right_inv y := by
    have hj : y ∈ T (Classical.choose (hTcov y)) := Classical.choose_spec (hTcov y)
    have hx : (h (Classical.choose (hTcov y))).symm y ∈ S (Classical.choose (hTcov y)) := by
      rw [← himage] at hj
      obtain ⟨x, hx, hxy⟩ := hj
      rw [(h _).symm_apply_eq.mpr hxy.symm]
      exact hx
    have hi := Classical.choose_spec (hScov ((h (Classical.choose (hTcov y))).symm y))
    change h (Classical.choose (hScov _)) _ = y
    rw [hagree _ _ _ hi hx]
    exact (h _).apply_symm_apply y
  continuous_toFun := by
    refine (locallyFinite_of_finite S).continuous (iUnion_eq_univ_iff.2 hScov) hS fun i => ?_
    refine (h i).continuous.continuousOn.congr fun x hx => ?_
    exact hagree _ i x (Classical.choose_spec (hScov x)) hx
  continuous_invFun := by
    refine (locallyFinite_of_finite T).continuous (iUnion_eq_univ_iff.2 hTcov) hT fun i => ?_
    refine (h i).symm.continuous.continuousOn.congr fun y hy => ?_
    exact hagree' _ i y (Classical.choose_spec (hTcov y)) hy

/-- The glued homeomorphism restricts to each given piece. -/
theorem homeomorphOfClosedCover_apply (S : ι → Set X) (T : ι → Set Y)
    (hS : ∀ i, IsClosed (S i)) (hT : ∀ i, IsClosed (T i))
    (hScov : ∀ x, ∃ i, x ∈ S i) (hTcov : ∀ y, ∃ i, y ∈ T i)
    (h : ι → X ≃ₜ Y) (himage : ∀ i, h i '' S i = T i)
    (hagree : ∀ i j x, x ∈ S i → x ∈ S j → h i x = h j x)
    (hagree' : ∀ i j y, y ∈ T i → y ∈ T j → (h i).symm y = (h j).symm y)
    {i : ι} {x : X} (hx : x ∈ S i) :
    homeomorphOfClosedCover S T hS hT hScov hTcov h himage hagree hagree' x = h i x :=
  hagree _ i x (Classical.choose_spec (hScov x)) hx

end FiniteAvalanches.Electrical.StatementGeometry
