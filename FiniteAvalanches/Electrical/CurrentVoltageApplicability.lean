import FiniteAvalanches.Electrical.Geometry.CurrentSourceVoltage
import FiniteAvalanches.Electrical.Reference.Voltage
import FiniteAvalanches.Electrical.Physical.CurrentRegularStar
import FiniteAvalanches.Electrical.SplitStep.ActualConnectivity

/-! Voltage characterizations on the actual copied lattice and grounded split carriers. -/
namespace FiniteAvalanches.Electrical.CurrentVoltageApplicability
open LatticeProb StatementGeometry Plane.SourceLattice
open Source.CurrentDomain SplitStep ChordSplit CurrentRegularPhysical
open scoped Classical
noncomputable section

variable (D : Finset (Site 2)) (P : OneSet D)

/-- Distinctness follows from the actual contracted vertex carrier. -/
theorem original_terminals_ne : alpha D P ≠ beta D P := by
  intro h
  cases h

variable (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
  (marked : MarkedCopy D P)

/-- The legacy boundary-data extension has the full source characterization here. -/
theorem actual_legacy_voltage_spec :
    source_spec (originalGraph D P marked) (alpha D P) (beta D P)
      (Source.voltage (originalGraph D P marked) (alpha D P) (beta D P)
        (Repair8.graph_connected D P hD marked).preconnected) := by
  exact Source.voltage_spec _ _ _ (original_terminals_ne D P) _

/-- Uniqueness identifies the two existing choices on every actual admitted network. -/
theorem actual_legacy_voltage_eq_repair8 :
    Source.voltage (originalGraph D P marked) (alpha D P) (beta D P)
      (Repair8.graph_connected D P hD marked).preconnected =
      Repair8.voltage D P hD marked := by
  exact Repair8.voltage_unique D P hD marked _
    (actual_legacy_voltage_spec D P hD marked)

/-- The separately characterized source object equals the actual reference voltage. -/
theorem actual_source_voltage_eq_repair8 :
    source_voltage (originalGraph D P marked) (alpha D P) (beta D P)
      (original_terminals_ne D P) (Repair8.graph_connected D P hD marked).preconnected =
      Repair8.voltage D P hD marked := by
  exact (source_voltage_eq_voltage _ _ _ (original_terminals_ne D P) _).trans
    (actual_legacy_voltage_eq_repair8 D P hD marked)

/-- The minimum-corner copied graph is the identical original endpoint family. -/
theorem minimum_graph_voltage_eq_repair8 :
    Source.voltage (sourceGraph D P marked) (alpha D P) (beta D P)
      (Repair8.graph_connected D P hD marked).preconnected =
      Repair8.voltage D P hD marked := by
  exact actual_legacy_voltage_eq_repair8 D P hD marked

/-- Pullback keeps both collapsed root sets and every free-vertex equation. -/
theorem actual_legacy_pullback_spec :
    let phi := Source.voltage (originalGraph D P marked) (alpha D P) (beta D P)
      (Repair8.graph_connected D P hD marked).preconnected
    (∀ x : Site 2, x ∉ D → phi (project D P x) = 0) ∧
    (∀ x : Site 2, x ∈ P.val.image Subtype.val → phi (project D P x) = 1) ∧
    (∀ x : Vertex D P, x ≠ alpha D P → x ≠ beta D P →
      laplacian (copyA D P marked) (copyB D P marked) phi x = 0) := by
  dsimp only
  have hp := actual_legacy_voltage_spec D P hD marked
  refine ⟨?_, ?_, hp.2.2⟩
  · intro x hx
    rw [(project_eq_alpha_iff D P x).mpr hx]
    exact hp.1
  · intro x hx
    rw [(project_eq_beta_iff D P x).mpr hx]
    exact hp.2.1

/-- Once-per-copy energy is unchanged by the characterized alias transport. -/
theorem actual_conductance_eq_reference_energy :
    Source.effectiveConductance (originalGraph D P marked) (alpha D P) (beta D P)
      (original_terminals_ne D P) (Repair8.graph_connected D P hD marked).preconnected =
      energy (copyA D P marked) (copyB D P marked) (Repair8.voltage D P hD marked) := by
  change energy _ _ _ = _
  rw [actual_legacy_voltage_eq_repair8 D P hD marked]
  rfl

variable {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
  copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
  (i : ℕ) (hi0 : 0 < i) (him : i < m)

/-- Strict interior splits derive connectivity before either voltage is selected. -/
theorem actual_grounded_voltage_spec :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    let hc := actual_grounded_preconnected D P hD marked copies i hi0 him
    source_spec K (.inr false) (.inr true) (Source.voltage K (.inr false) (.inr true) hc) := by
  dsimp only
  exact Source.voltage_spec _ _ _ (grounded_terminals_ne D P) _

/-- The identified source voltage is the retained constructor at the derived terminals. -/
theorem actual_grounded_source_voltage_eq_legacy :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    let hc := actual_grounded_preconnected D P hD marked copies i hi0 him
    source_voltage K (.inr false) (.inr true) (grounded_terminals_ne D P) hc =
      Source.voltage K (.inr false) (.inr true) hc := by
  dsimp only
  exact source_voltage_eq_voltage _ _ _ (grounded_terminals_ne D P) _

/-- The current original diagonal transport uses the actual source energy normalization. -/
theorem actual_total_response_eq_source_energy :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    let hc := actual_grounded_preconnected D P hD marked copies i hi0 him
    totalResponse D P hD marked copies i = energy K.left K.right
      (source_voltage K (.inr false) (.inr true) (grounded_terminals_ne D P) hc) := by
  dsimp only
  rw [source_voltage_eq_voltage]
  exact (actual_conductance_eq_totalResponse D P hD marked copies i hi0 him).symm

end
end FiniteAvalanches.Electrical.CurrentVoltageApplicability
