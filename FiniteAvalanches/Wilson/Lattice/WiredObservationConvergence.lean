import FiniteAvalanches.Wilson.Lattice.WiredObservationCoupling
import Mathlib.MeasureTheory.Integral.Indicator

/-! Joint wired observations converge to finite lattice Wilson queries. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Under a common row coupling, every finite wired joint observation agrees
with the lattice sampler in all sufficiently large boxes, almost surely. -/
theorem wilsonRows_ae_eventually_wiredObservationRowEvent_iff (R : RootPair)
    (x : ℕ → Site 2) (ka : Cursor (Site 2))
    (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hD : ∀ z ∈ D, ∃ i < n, x i = z) :
    ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop,
      (rows ∈ wiredObservationRowEvent R B x (kb B) n E D pe pc ↔
        rows ∈ samplerEvent R ((List.range n).map x) E D pe pc) := by
  have hreal : ∀ᵐ rows ∂wilsonRows, ∀ B : ℕ,
      rows ∈ wiredRowRealizationEvent R B (fun i => wiredSite B (x i)) (kb B) n := by
    apply ae_all_iff.mpr
    intro B
    exact wilsonRows_ae_wiredRowRealization R B (fun i => wiredSite B (x i)) (kb B) n
  filter_upwards [wilsonRows_lattice_ae_finite_branch_horizon R x ka n,
    samplerRun_ae_success R ((List.range n).map x), hreal] with rows hhit hs hR
  obtain ⟨N, hN⟩ := hhit
  obtain ⟨out, hout⟩ := hs
  filter_upwards [eventually_walkSegments_inBox x rows n N] with B hbox
  have hconf : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j) := by
    intro i hi j hj
    exact hbox i hi j (lt_of_le_of_lt hj (hN i hi))
  exact wiredObservationRowEvent_iff_samplerEvent_of_confined R B N x ka (kb B)
    rows n out hN hconf hout (hR B) E D pe pc hE hD

/-- The original-copy finite wired joint-observation probabilities converge
to the actual finite lattice Wilson sampler probabilities. -/
theorem finiteUniformLaw_wiredObservationCylinder_tendsto (R : RootPair)
    (x : ℕ → Site 2) (ka : Cursor (Site 2))
    (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hD : ∀ z ∈ D, ∃ i < n, x i = z) :
    Tendsto (fun B => finiteUniformLaw R B (wiredObservationCylinder R B E D pe pc)) atTop
      (nhds (wilsonRows (samplerEvent R ((List.range n).map x) E D pe pc))) := by
  have ht := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (measurableSet_samplerEvent R ((List.range n).map x) E D pe pc)
    (fun B => measurableSet_wiredObservationRowEvent R B x (kb B) n E D pe pc)
    (wilsonRows_ae_eventually_wiredObservationRowEvent_iff R x ka kb n E D pe pc hE hD)
  have he : (fun B => wilsonRows (wiredObservationRowEvent R B x (kb B) n E D pe pc)) =
      fun B => finiteUniformLaw R B (wiredObservationCylinder R B E D pe pc) := by
    funext B
    exact wilsonRows_wiredObservationRowEvent_eq R B x (kb B) n E D pe pc hE hD
  rw [he] at ht
  exact ht

end
end FiniteAvalanches.Wilson.Lattice
