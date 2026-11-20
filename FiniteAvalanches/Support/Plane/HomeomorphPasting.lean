import FiniteAvalanches.Support.Plane.DilationIsotopy
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Piecewise

/-!
# Pasting homeomorphisms along a boundary

Homeomorphisms that send a set to the same image and agree on its frontier
can be pasted to form a homeomorphism.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Filter
open scoped Topology

noncomputable section

/-- Paste two homeomorphisms along the frontier of a set when they send the set
to the same image. -/
def homeomorphPaste {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : X ≃ₜ Y) (K : Set X) (himage : f '' K = g '' K)
    (hboundary : ∀ x ∈ frontier K, f x = g x) : X ≃ₜ Y := by
  classical
  let L := f '' K
  have hfmem (x : X) : f x ∈ L ↔ x ∈ K := by
    simp only [L, f.image_eq_preimage_symm, mem_preimage, f.symm_apply_apply]
  have hgmem (x : X) : g x ∈ L ↔ x ∈ K := by
    rw [show L = g '' K from himage]
    simp only [g.image_eq_preimage_symm, mem_preimage, g.symm_apply_apply]
  have hinverse : ∀ y ∈ frontier L, f.symm y = g.symm y := by
    intro y hy
    have hy' : y ∈ f '' frontier K := by
      rw [f.image_frontier]
      exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    calc
      f.symm (f x) = x := f.symm_apply_apply x
      _ = g.symm (f x) := by rw [hboundary x hx, g.symm_apply_apply]
  refine {
    toFun := K.piecewise f g
    invFun := L.piecewise f.symm g.symm
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := f.continuous.piecewise hboundary g.continuous
    continuous_invFun := f.symm.continuous.piecewise hinverse g.symm.continuous
  }
  · intro x
    by_cases hx : x ∈ K
    · simp only [Set.piecewise, hx, if_true, (hfmem x).2 hx, f.symm_apply_apply]
    · simp only [Set.piecewise, hx, if_false, mt (hgmem x).1 hx, g.symm_apply_apply]
  · intro y
    by_cases hy : y ∈ L
    · have hx : f.symm y ∈ K := (hfmem (f.symm y)).1 (by simpa only [f.apply_symm_apply] using hy)
      simp only [Set.piecewise, hy, if_true, hx, f.apply_symm_apply]
    · have hx : g.symm y ∉ K := by
        intro hx
        exact hy (by simpa only [g.apply_symm_apply] using (hgmem (g.symm y)).2 hx)
      simp only [Set.piecewise, hy, if_false, hx, g.apply_symm_apply]

/-- The pasted homeomorphism agrees with its first factor on the chosen set. -/
theorem homeomorphPaste_apply_of_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : X ≃ₜ Y) (K : Set X) (himage : f '' K = g '' K)
    (hboundary : ∀ x ∈ frontier K, f x = g x) {x : X} (hx : x ∈ K) :
    homeomorphPaste f g K himage hboundary x = f x := by
  classical
  change K.piecewise f g x = f x
  simp only [Set.piecewise, hx, if_true]

/-- The pasted homeomorphism agrees with its second factor outside the set. -/
theorem homeomorphPaste_apply_of_notMem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : X ≃ₜ Y) (K : Set X) (himage : f '' K = g '' K)
    (hboundary : ∀ x ∈ frontier K, f x = g x) {x : X} (hx : x ∉ K) :
    homeomorphPaste f g K himage hboundary x = g x := by
  classical
  change K.piecewise f g x = g x
  simp only [Set.piecewise, hx, if_false]

/-- If a plane homeomorphism and an oriented chart agree on the boundary of a
compact set and have the same image of it, the homeomorphism agrees on that
set with an oriented chart. -/
theorem exists_orientedChart_agree_on_compact
    (f : Source.Plane ≃ₜ Source.Plane) (c : Source.OrientedChart)
    (K : Set Source.Plane) (hK : IsCompact K)
    (himage : f '' K = c.map '' K)
    (hboundary : ∀ x ∈ frontier K, f x = c.map x) :
    ∃ d : Source.OrientedChart, ∀ x ∈ K, d.map x = f x := by
  let F := homeomorphPaste f c.map K himage hboundary
  have hne : K ≠ univ := by
    intro h
    exact noncompact_univ Source.Plane (h ▸ hK)
  obtain ⟨z, hz⟩ : ∃ z, z ∉ K := by
    by_contra h
    apply hne
    exact eq_univ_iff_forall.mpr (by simpa only [not_exists, not_not] using h)
  have hloc : F =ᶠ[𝓝 z] c.map := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with x hx
    exact homeomorphPaste_apply_of_notMem f c.map K himage hboundary hx
  refine ⟨orientedChartOfLocallyEq F c z hloc, ?_⟩
  intro x hx
  exact homeomorphPaste_apply_of_mem f c.map K himage hboundary hx

end
end FiniteAvalanches.Electrical.StatementGeometry
