import FiniteAvalanches.Support.Plane.LoopCancellation
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Injective path reductions through compact quotients

A continuous quotient of a closed subset of the unit interval yields an
injective path when its fibers are exactly the equal-value fibers of a path.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- An endpoint-preserving quotient of a closed parameter set with precisely the
fibers of a path produces an injective path contained in its image. -/
theorem exists_injective_path_of_compact_quotient
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (F : Set unitInterval) (hF : IsClosed F) (h0 : (0 : unitInterval) ∈ F)
    (h1 : (1 : unitInterval) ∈ F) (g : unitInterval → unitInterval)
    (hg : Continuous g) (hg0 : g 0 = 0) (hg1 : g 1 = 1)
    (hsurj : ∀ u : unitInterval, ∃ t ∈ F, g t = u)
    (hfiber : ∀ s ∈ F, ∀ t ∈ F, g s = g t ↔ p s = p t) :
    ∃ q : Path x y, Function.Injective q ∧ range q ⊆ range p := by
  have hcompact : IsCompact F := isCompact_univ.of_isClosed_subset hF (subset_univ F)
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hcompact
  let G : F → unitInterval := fun t => g t.1
  have hG : Continuous G := hg.comp continuous_subtype_val
  have hGsurj : Function.Surjective G := by
    intro u
    obtain ⟨t, htF, ht⟩ := hsurj u
    exact ⟨⟨t, htF⟩, ht⟩
  let GM : C(F, unitInterval) := ⟨G, hG⟩
  have hquot : Topology.IsQuotientMap GM := .of_surjective_continuous hGsurj hG
  let P : C(F, X) := ⟨fun t => p t.1, p.continuous.comp continuous_subtype_val⟩
  have hfactor : Function.FactorsThrough P GM := by
    intro s t hst
    exact (hfiber s.1 s.2 t.1 t.2).mp hst
  let Q : C(unitInterval, X) := Topology.IsQuotientMap.lift (f := GM) hquot P hfactor
  have hcomm : ∀ t : F, Q (G t) = p t.1 := by
    intro t
    have h := congrFun (congrArg DFunLike.coe (Topology.IsQuotientMap.lift_comp (f := GM) hquot P hfactor)) t
    exact h
  have hsource : Q 0 = x := by
    have h := hcomm ⟨0, h0⟩
    simpa only [G, hg0, Path.source] using h
  have htarget : Q 1 = y := by
    have h := hcomm ⟨1, h1⟩
    simpa only [G, hg1, Path.target] using h
  let q : Path x y := ⟨Q, hsource, htarget⟩
  refine ⟨q, ?_, ?_⟩
  · intro a b hab
    obtain ⟨s, hsF, hs⟩ := hsurj a
    obtain ⟨t, htF, ht⟩ := hsurj b
    have hpst : p s = p t := by
      have hqs := hcomm ⟨s, hsF⟩
      have hqt := hcomm ⟨t, htF⟩
      change Q (g s) = p s at hqs
      change Q (g t) = p t at hqt
      rw [hs] at hqs
      rw [ht] at hqt
      exact hqs.symm.trans (hab.trans hqt)
    exact hs.symm.trans (((hfiber s hsF t htF).mpr hpst).trans ht)
  · rintro z ⟨t, rfl⟩
    obtain ⟨s, hsF, hs⟩ := hsurj t
    refine ⟨s, ?_⟩
    have h := hcomm ⟨s, hsF⟩
    change Q (g s) = p s at h
    rw [hs] at h
    exact h.symm

end FiniteAvalanches.Electrical.StatementGeometry
