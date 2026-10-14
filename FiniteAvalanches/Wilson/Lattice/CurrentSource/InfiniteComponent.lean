import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.CofiniteComponent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentInfiniteComponent
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- Two literal induced components with a common original site are identical. -/
theorem component_eq_of_common_site (U : Set (Site 2)) (c d : U) (z : Site 2)
    (hc : z ∈ JointExterior.component U c) (hd : z ∈ JointExterior.component U d) :
    JointExterior.component U c = JointExterior.component U d := by
  obtain ⟨hzU, hzc⟩ := hc
  obtain ⟨_hzU, hzd⟩ := hd
  have hcd := hzc.symm.trans hzd
  ext x
  constructor
  · rintro ⟨hxU, hxc⟩
    exact ⟨hxU, hxc.trans hcd⟩
  · rintro ⟨hxU, hxd⟩
    exact ⟨hxU, hxd.trans hcd.symm⟩

/-- The actual cofinite component is the unique infinite component; no default
component or one-ended UST statement is assumed. -/
theorem cofinite_component_is_unique_infinite (U : Set (Site 2)) (c : U)
    (hc : (JointExterior.component U c)ᶜ.Finite) :
    (JointExterior.component U c).Infinite ∧
      ∀ d : U, (JointExterior.component U d).Infinite →
        JointExterior.component U d = JointExterior.component U c := by
  constructor
  · exact Set.infinite_of_finite_compl hc
  · intro d hd
    obtain ⟨z, hzd, hzc⟩ := (hd.sdiff hc).nonempty
    have hzc' : z ∈ JointExterior.component U c := by
      simpa only [Set.mem_compl_iff, not_not] using hzc
    exact component_eq_of_common_site U d c z hzd hzc'

/-- Current source487: the component of gamma outside the actual square has an
ordinary existence, cofinite characterization, and unique infinite identity. -/
theorem exists_unique_infinite_exterior_component (γ : Set (Site 2))
    (hγ : γᶜ.Finite) (h : ℕ) :
    ∃ c : ↥(γ \ box 2 (2 * h)),
      (JointExterior.component (γ \ box 2 (2 * h)) c)ᶜ.Finite ∧
      (JointExterior.component (γ \ box 2 (2 * h)) c).Infinite ∧
      ∀ d : ↥(γ \ box 2 (2 * h)),
        (JointExterior.component (γ \ box 2 (2 * h)) d).Infinite →
          JointExterior.component (γ \ box 2 (2 * h)) d =
            JointExterior.component (γ \ box 2 (2 * h)) c := by
  obtain ⟨c, hc⟩ := JointCofiniteComponent.exists_cofinite_component γ hγ (2 * h)
  obtain ⟨hi, hu⟩ := cofinite_component_is_unique_infinite _ c hc
  exact ⟨c, hc, hi, hu⟩

/-- Any two geometry witnesses with cofinite components select the same source object. -/
theorem cofinite_component_choice_independent (U : Set (Site 2)) (c d : U)
    (hc : (JointExterior.component U c)ᶜ.Finite)
    (hd : (JointExterior.component U d)ᶜ.Finite) :
    JointExterior.component U c = JointExterior.component U d := by
  obtain ⟨_hi, hu⟩ := cofinite_component_is_unique_infinite U d hd
  exact hu c (Set.infinite_of_finite_compl hc)

end
end FiniteAvalanches.Wilson.Lattice.CurrentInfiniteComponent
