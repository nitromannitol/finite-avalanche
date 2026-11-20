import FiniteAvalanches.Support.Plane.GeometricDual
import FiniteAvalanches.Support.Plane.DualDrawingFromArms
import Mathlib.Topology.Subpath

/-!
# Crossing stubs

The two quarter-length halves of a parametrized crossing have disjoint
interiors and meet only at the crossing.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Set unitInterval Source BSST

/-- The parameter on a crossing stub on the chosen side. -/
noncomputable def crossingStubParameter (side : Bool) (t : unitInterval) : unitInterval :=
  if side then ⟨(3 - (t : ℝ)) / 4, by
    constructor <;> linarith [t.property.1, t.property.2]⟩
  else ⟨(1 + (t : ℝ)) / 4, by
    constructor <;> linarith [t.property.1, t.property.2]⟩

/-- The quarter-length side of a parametrized crossing. -/
noncomputable def crossingStub {X : Type*} [TopologicalSpace X] (q : unitInterval → X)
    (hq : Continuous q) (side : Bool) :
    Path (q (crossingStubParameter side 0)) (q (crossingStubParameter side 1)) where
  toFun := fun t => q (crossingStubParameter side t)
  continuous_toFun := by
    apply hq.comp
    apply continuous_induced_rng.mpr
    cases side <;> fun_prop
  source' := rfl
  target' := rfl

/-- Crossing-stub parameters are injective. -/
theorem crossingStubParameter_injective (side : Bool) :
    Function.Injective (crossingStubParameter side) := by
  intro a b h
  have h' := congrArg Subtype.val h
  cases side <;> simp only [crossingStubParameter, Bool.false_eq_true, ↓reduceIte,
    ] at h'
  all_goals apply Subtype.ext; linarith

/-- An injective crossing induces injective stubs. -/
theorem crossingStub_injective {X : Type*} [TopologicalSpace X]
    (q : unitInterval → X) (hq : Continuous q) (hinj : Function.Injective q) (side : Bool) :
    Function.Injective (crossingStub q hq side) :=
  hinj.comp (crossingStubParameter_injective side)

/-- Both stubs end at the midpoint of the crossing. -/
theorem crossingStubParameter_one (side : Bool) :
    crossingStubParameter side 1 = ⟨1 / 2, by norm_num⟩ := by
  apply Subtype.ext
  cases side <;> norm_num [crossingStubParameter]

/-- A nonterminal point of a stub lies strictly on its chosen side. -/
theorem crossingStubParameter_side (side : Bool) (t : unitInterval) (ht : t ≠ 1) :
    (side = false → (crossingStubParameter side t : ℝ) < 1 / 2) ∧
      (side = true → 1 / 2 < (crossingStubParameter side t : ℝ)) := by
  have ht' : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
    (fun h => ht (Subtype.ext h))
  cases side <;> norm_num [crossingStubParameter] <;> linarith

/-- Opposite stubs of one injective crossing meet only at its midpoint. -/
theorem crossingStub_inter_opposite {X : Type*} [TopologicalSpace X]
    (q : unitInterval → X) (hq : Continuous q) (hinj : Function.Injective q) :
    range (crossingStub q hq false) ∩ range (crossingStub q hq true) =
      {q ⟨1 / 2, by norm_num⟩} := by
  apply subset_antisymm
  · rintro z ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    have heq := hinj ht
    have heq' := congrArg Subtype.val heq
    have hs := s.property.2
    have ht' := t.property.2
    have hs1 : s = 1 := by
      apply Subtype.ext
      simp only [crossingStubParameter, Bool.false_eq_true, ↓reduceIte] at heq'
      change (s : ℝ) = 1
      linarith
    change q (crossingStubParameter false s) = _
    rw [hs1, crossingStubParameter_one]
  · intro z hz
    simp only [mem_singleton_iff] at hz
    subst z
    refine ⟨?_, ?_⟩
    · exact ⟨1, by rw [show (crossingStub q hq false) 1 =
        q (crossingStubParameter false 1) from rfl, crossingStubParameter_one]⟩
    · exact ⟨1, by rw [show (crossingStub q hq true) 1 =
        q (crossingStubParameter true 1) from rfl, crossingStubParameter_one]⟩

/-- Stubs of distinct disjoint crossings are disjoint. -/
theorem crossingStub_disjoint_of_disjoint {X : Type*} [TopologicalSpace X]
    (q q' : unitInterval → X) (hq : Continuous q) (hq' : Continuous q')
    (side side' : Bool) (hd : Disjoint (range q) (range q')) :
    Disjoint (range (crossingStub q hq side)) (range (crossingStub q' hq' side')) := by
  apply hd.mono
  · rintro z ⟨t, rfl⟩
    exact ⟨crossingStubParameter side t, rfl⟩
  · rintro z ⟨t, rfl⟩
    exact ⟨crossingStubParameter side' t, rfl⟩

end FiniteAvalanches.Electrical.StatementGeometry
