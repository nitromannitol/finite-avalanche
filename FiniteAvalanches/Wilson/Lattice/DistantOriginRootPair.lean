import FiniteAvalanches.Wilson.Lattice.OriginWiredObservationProbability
import FiniteAvalanches.Wilson.Lattice.WiredCylinderLaw

/-! A distant auxiliary root for origin-and-sink wired explorations. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A site one step beyond the positive horizontal side of a wired box. -/
def distantOriginRoot (B : ℕ) : Site 2 :=
  fun i => if i = 0 then (B : ℤ) + 1 else 0

/-- The auxiliary site is outside the corresponding wired box. -/
theorem distantOriginRoot_not_inBox (B : ℕ) : ¬FiniteWired.inBox B (distantOriginRoot B) := by
  intro h
  have h0 := (h 0).2
  simp only [distantOriginRoot, ↓reduceIte] at h0
  omega

/-- The auxiliary site is distinct from the lattice origin. -/
theorem distantOriginRoot_ne_zero (B : ℕ) : distantOriginRoot B ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [distantOriginRoot, ↓reduceIte, Pi.zero_apply] at h0
  omega

/-- The origin and a distant site form disjoint, nonempty root sets. -/
def distantOriginRootPair (B : ℕ) : RootPair where
  zero := {0}
  one := {distantOriginRoot B}
  disjoint := by
    apply Set.disjoint_left.mpr
    intro z hz ho
    simp only [Set.mem_singleton_iff] at hz ho
    exact distantOriginRoot_ne_zero B (ho.symm.trans hz)
  zero_nonempty := ⟨0, rfl⟩
  one_nonempty := ⟨distantOriginRoot B, rfl⟩

/-- Wiring the auxiliary site leaves precisely the origin and sink as roots. -/
theorem wiredRoots_distantOriginRootPair (B : ℕ) :
    (wiredRoots (distantOriginRootPair B) B).val = wiredOriginAndSink B := by
  ext v
  cases v with
  | none =>
    change (False ∨ True) ↔ (none = none ∨ none = some (wiredOrigin B))
    simp only [false_or, true_iff, eq_self_iff_true, true_or]
  | some a =>
    have hne : FiniteWired.site a ≠ distantOriginRoot B := by
      intro he
      apply distantOriginRoot_not_inBox B
      rw [← he]
      exact fun i => (a i).property
    have horigin : FiniteWired.site (wiredOrigin B) = (0 : Site 2) := by
      funext i
      rfl
    have hzero : FiniteWired.site a = 0 ↔ a = wiredOrigin B := by
      constructor
      · intro h
        apply FiniteWired.site_injective B
        exact h.trans horigin.symm
      · rintro rfl
        exact horigin
    change (FiniteWired.site a = 0 ∨ FiniteWired.site a = distantOriginRoot B) ↔
      (some a = none ∨ some a = some (wiredOrigin B))
    simp only [hne, or_false, Option.some_ne_none, false_or, Option.some.injEq, hzero]

end
end FiniteAvalanches.Wilson.Lattice
