import FiniteAvalanches.Support.Plane.CircleCut
import Mathlib.Order.Hom.Set

/-!
# Extension of increasing open-interval homeomorphisms

A strictly increasing homeomorphism of the open unit interval extends
uniquely to an increasing homeomorphism of the closed unit interval.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- Extend an open-interval map by the identity at the endpoints. -/
noncomputable def openIntervalExtend (g : Ioo (0 : ℝ) 1 → Ioo (0 : ℝ) 1)
    (x : unitInterval) : unitInterval := by
  by_cases hx : (x : ℝ) ∈ Ioo (0 : ℝ) 1
  · exact ⟨g ⟨x, hx⟩, Ioo_subset_Icc_self (g ⟨x, hx⟩).property⟩
  · exact x

/-- In the open interval the extension agrees with the original map. -/
theorem openIntervalExtend_apply_interior (g : Ioo (0 : ℝ) 1 → Ioo (0 : ℝ) 1)
    (x : unitInterval) (hx : (x : ℝ) ∈ Ioo (0 : ℝ) 1) :
    (openIntervalExtend g x : ℝ) = g ⟨x, hx⟩ := by
  simp only [openIntervalExtend, dif_pos hx]

/-- The extension fixes both endpoints. -/
theorem openIntervalExtend_endpoints (g : Ioo (0 : ℝ) 1 → Ioo (0 : ℝ) 1) :
    openIntervalExtend g 0 = 0 ∧ openIntervalExtend g 1 = 1 := by
  constructor <;> simp [openIntervalExtend]

/-- An increasing open-interval bijection extends to an increasing closed
interval homeomorphism. -/
theorem exists_unitInterval_homeomorph_of_openInterval
    (g : Ioo (0 : ℝ) 1 ≃ₜ Ioo (0 : ℝ) 1) (hg : StrictMono g) :
    ∃ f : unitInterval ≃ₜ unitInterval, StrictMono f ∧
      (∀ x : Ioo (0 : ℝ) 1, (f ⟨x, Ioo_subset_Icc_self x.property⟩ : ℝ) = g x) := by
  let f := openIntervalExtend g
  have hf0 : f 0 = 0 := (openIntervalExtend_endpoints g).1
  have hf1 : f 1 = 1 := (openIntervalExtend_endpoints g).2
  have hm : StrictMono f := by
    intro x y hxy
    by_cases hx : x = 0
    · subst x
      rw [hf0]
      by_cases hy : y = 1
      · subst y
        rw [hf1]
        norm_num
      · have hyi : (y : ℝ) ∈ Ioo (0 : ℝ) 1 := by
          constructor
          · exact hxy
          · have hylt : (y : ℝ) < 1 := lt_of_le_of_ne y.property.2 (fun h => hy (Subtype.ext h))
            exact hylt
        change (0 : ℝ) < f y
        rw [openIntervalExtend_apply_interior g y hyi]
        exact (g ⟨y, hyi⟩).property.1
    · by_cases hy : y = 1
      · subst y
        rw [hf1]
        have hxi : (x : ℝ) ∈ Ioo (0 : ℝ) 1 := by
          constructor
          · exact lt_of_le_of_ne x.property.1 (fun h => hx (Subtype.ext h.symm))
          · exact hxy
        change (f x : ℝ) < 1
        rw [openIntervalExtend_apply_interior g x hxi]
        exact (g ⟨x, hxi⟩).property.2
      · have hxi : (x : ℝ) ∈ Ioo (0 : ℝ) 1 := by
          constructor
          · exact lt_of_le_of_ne x.property.1 (fun h => hx (Subtype.ext h.symm))
          · exact lt_trans hxy (lt_of_le_of_ne y.property.2 (fun h => hy (Subtype.ext h)))
        have hyi : (y : ℝ) ∈ Ioo (0 : ℝ) 1 := by
          constructor
          · exact lt_trans hxi.1 hxy
          · exact lt_of_le_of_ne y.property.2 (fun h => hy (Subtype.ext h))
        change (f x : ℝ) < f y
        rw [openIntervalExtend_apply_interior g x hxi, openIntervalExtend_apply_interior g y hyi]
        exact hg hxy
  have hs : Function.Surjective f := by
    intro y
    by_cases hy0 : y = 0
    · exact ⟨0, by rw [hf0, hy0]⟩
    by_cases hy1 : y = 1
    · exact ⟨1, by rw [hf1, hy1]⟩
    have hyi : (y : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact lt_of_le_of_ne y.property.1 (fun h => hy0 (Subtype.ext h.symm))
      · exact lt_of_le_of_ne y.property.2 (fun h => hy1 (Subtype.ext h))
    obtain ⟨x, hx⟩ := g.surjective ⟨y, hyi⟩
    refine ⟨⟨x, Ioo_subset_Icc_self x.property⟩, ?_⟩
    apply Subtype.ext
    rw [openIntervalExtend_apply_interior g _ x.property]
    exact congrArg Subtype.val hx
  let e := StrictMono.orderIsoOfSurjective f hm hs
  refine ⟨e.toHomeomorph, e.strictMono, ?_⟩
  intro x
  exact openIntervalExtend_apply_interior g _ x.property

end FiniteAvalanches.Electrical.StatementGeometry
