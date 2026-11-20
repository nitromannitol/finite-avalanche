import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

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

/-- Three homeomorphisms agreeing on the overlaps of two closed covers by three
pieces glue to a homeomorphism restricting to each of them. -/
theorem exists_homeomorph_glue_three (S₀ S₁ S₂ : Set X) (T₀ T₁ T₂ : Set Y)
    (hS₀ : IsClosed S₀) (hS₁ : IsClosed S₁) (hS₂ : IsClosed S₂)
    (hT₀ : IsClosed T₀) (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂)
    (hScov : ∀ x, x ∈ S₀ ∨ x ∈ S₁ ∨ x ∈ S₂) (hTcov : ∀ y, y ∈ T₀ ∨ y ∈ T₁ ∨ y ∈ T₂)
    (h₀ h₁ h₂ : X ≃ₜ Y) (him₀ : h₀ '' S₀ = T₀) (him₁ : h₁ '' S₁ = T₁) (him₂ : h₂ '' S₂ = T₂)
    (h01 : ∀ x ∈ S₀ ∩ S₁, h₀ x = h₁ x) (h02 : ∀ x ∈ S₀ ∩ S₂, h₀ x = h₂ x)
    (h12 : ∀ x ∈ S₁ ∩ S₂, h₁ x = h₂ x)
    (h01' : ∀ y ∈ T₀ ∩ T₁, h₀.symm y = h₁.symm y) (h02' : ∀ y ∈ T₀ ∩ T₂, h₀.symm y = h₂.symm y)
    (h12' : ∀ y ∈ T₁ ∩ T₂, h₁.symm y = h₂.symm y) :
    ∃ h : X ≃ₜ Y, (∀ x ∈ S₀, h x = h₀ x) ∧ (∀ x ∈ S₁, h x = h₁ x) ∧ (∀ x ∈ S₂, h x = h₂ x) := by
  let S : Fin 3 → Set X := ![S₀, S₁, S₂]
  let T : Fin 3 → Set Y := ![T₀, T₁, T₂]
  let h : Fin 3 → X ≃ₜ Y := ![h₀, h₁, h₂]
  have hS : ∀ i, IsClosed (S i) := by
    intro i
    fin_cases i
    exacts [hS₀, hS₁, hS₂]
  have hT : ∀ i, IsClosed (T i) := by
    intro i
    fin_cases i
    exacts [hT₀, hT₁, hT₂]
  have hScov' : ∀ x, ∃ i, x ∈ S i := by
    intro x
    rcases hScov x with hx | hx | hx
    exacts [⟨0, hx⟩, ⟨1, hx⟩, ⟨2, hx⟩]
  have hTcov' : ∀ y, ∃ i, y ∈ T i := by
    intro y
    rcases hTcov y with hy | hy | hy
    exacts [⟨0, hy⟩, ⟨1, hy⟩, ⟨2, hy⟩]
  have himage : ∀ i, h i '' S i = T i := by
    intro i
    fin_cases i
    exacts [him₀, him₁, him₂]
  have hagree : ∀ i j x, x ∈ S i → x ∈ S j → h i x = h j x := by
    intro i j x hi hj
    fin_cases i <;> fin_cases j
    exacts [rfl, h01 x ⟨hi, hj⟩, h02 x ⟨hi, hj⟩, (h01 x ⟨hj, hi⟩).symm, rfl, h12 x ⟨hi, hj⟩,
      (h02 x ⟨hj, hi⟩).symm, (h12 x ⟨hj, hi⟩).symm, rfl]
  have hagree' : ∀ i j y, y ∈ T i → y ∈ T j → (h i).symm y = (h j).symm y := by
    intro i j y hi hj
    fin_cases i <;> fin_cases j
    exacts [rfl, h01' y ⟨hi, hj⟩, h02' y ⟨hi, hj⟩, (h01' y ⟨hj, hi⟩).symm, rfl, h12' y ⟨hi, hj⟩,
      (h02' y ⟨hj, hi⟩).symm, (h12' y ⟨hj, hi⟩).symm, rfl]
  refine ⟨homeomorphOfClosedCover S T hS hT hScov' hTcov' h himage hagree hagree', ?_, ?_, ?_⟩
  · exact fun x hx => homeomorphOfClosedCover_apply S T hS hT hScov' hTcov' h himage hagree
      hagree' (i := 0) hx
  · exact fun x hx => homeomorphOfClosedCover_apply S T hS hT hScov' hTcov' h himage hagree
      hagree' (i := 1) hx
  · exact fun x hx => homeomorphOfClosedCover_apply S T hS hT hScov' hTcov' h himage hagree
      hagree' (i := 2) hx

end FiniteAvalanches.Electrical.StatementGeometry
