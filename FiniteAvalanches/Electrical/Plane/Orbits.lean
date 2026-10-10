import FiniteAvalanches.Electrical.Plane.Darts
import Mathlib.Data.Fintype.EquivFin

/-! Actual finite permutation orbits, including fixed-point orbits. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical

/-- All points in one actual permutation orbit; fixed points are not discarded. -/
noncomputable def cyclePoints {X : Type*} [Fintype X] (f : Equiv.Perm X) (x : X) : Finset X :=
  Finset.univ.filter (f.SameCycle x)

@[simp] theorem mem_cyclePoints {X : Type*} [Fintype X] (f : Equiv.Perm X) (x y : X) :
    y ∈ cyclePoints f x ↔ f.SameCycle x y := by simp [cyclePoints]

theorem cyclePoints_nonempty {X : Type*} [Fintype X] (f : Equiv.Perm X) (x : X) :
    (cyclePoints f x).Nonempty := ⟨x,(mem_cyclePoints f x x).mpr (.refl f x)⟩

theorem isCycleOn_cyclePoints {X : Type*} [Fintype X] (f : Equiv.Perm X) (x : X) :
    f.IsCycleOn (cyclePoints f x) := by
  constructor
  · refine ⟨?_,f.injective.injOn,?_⟩
    · intro y hy
      simpa using hy
    · intro y hy
      refine ⟨f.symm y,?_,f.apply_symm_apply y⟩
      simpa using hy
  · intro y hy z hz
    exact ((mem_cyclePoints f x y).mp hy).symm.trans ((mem_cyclePoints f x z).mp hz)

/-- The orbit is enumerated once, starting at x, in the actual permutation order. -/
noncomputable def orbitEquiv {X : Type*} [Fintype X] (f : Equiv.Perm X) (x : X) :
    Fin (cyclePoints f x).card ≃ {y : X // f.SameCycle x y} :=
  Equiv.ofBijective (fun i => ⟨(f^i.val) x,by simpa only [Equiv.Perm.sameCycle_pow_right] using Equiv.Perm.SameCycle.refl f x⟩) (by
    constructor
    · intro i j h
      have hp := (isCycleOn_cyclePoints f x).pow_apply_eq_pow_apply (m := i.val) (n := j.val)
        ((mem_cyclePoints f x x).mpr (.refl f x))
      have hm := hp.mp (congrArg Subtype.val h)
      apply Fin.ext
      simpa only [Nat.ModEq,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hm
    · intro y
      obtain ⟨n,hn,he⟩ := (isCycleOn_cyclePoints f x).exists_pow_eq
        ((mem_cyclePoints f x x).mpr (.refl f x)) ((mem_cyclePoints f x y).mpr y.property)
      exact ⟨⟨n,hn⟩,Subtype.ext he⟩)

@[simp] theorem orbitEquiv_apply {X : Type*} [Fintype X] (f : Equiv.Perm X) (x : X)
    (i : Fin (cyclePoints f x).card) : (orbitEquiv f x i).val = (f^i.val) x := rfl

theorem pow_cyclePoints_card {X : Type*} [Fintype X] (f : Equiv.Perm X) (x : X) :
    (f^(cyclePoints f x).card) x = x :=
  (isCycleOn_cyclePoints f x).pow_card_apply ((mem_cyclePoints f x x).mpr (.refl f x))

theorem orbit_pow_inj {X : Type*} [Fintype X] (f : Equiv.Perm X) (x : X)
    {i j : ℕ} (hi : i < (cyclePoints f x).card) (hj : j < (cyclePoints f x).card)
    (h : (f^i) x = (f^j) x) : i = j := by
  have he := (orbitEquiv f x).injective (show orbitEquiv f x ⟨i,hi⟩ = orbitEquiv f x ⟨j,hj⟩ from Subtype.ext h)
  exact congrArg Fin.val he

/-- The unique position of a point on its actual finite orbit. -/
noncomputable def orbitIndex {X : Type*} [Fintype X] (f : Equiv.Perm X) (x y : X)
    (h : f.SameCycle x y) : Fin (cyclePoints f x).card :=
  (orbitEquiv f x).symm ⟨y,h⟩

theorem orbitIndex_spec {X : Type*} [Fintype X] (f : Equiv.Perm X) (x y : X)
    (h : f.SameCycle x y) : (f^(orbitIndex f x y h).val) x = y :=
  congrArg Subtype.val ((orbitEquiv f x).apply_symm_apply ⟨y,h⟩)

theorem orbitIndex_pow {X : Type*} [Fintype X] (f : Equiv.Perm X) (x : X)
    (i : ℕ) (hi : i < (cyclePoints f x).card) (h : f.SameCycle x ((f^i) x)) :
    (orbitIndex f x ((f^i) x) h).val = i :=
  orbit_pow_inj f x (orbitIndex f x _ h).isLt hi (orbitIndex_spec f x _ h)

end FiniteAvalanches.Electrical.Plane
