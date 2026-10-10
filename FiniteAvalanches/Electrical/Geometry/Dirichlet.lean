module

public import FiniteAvalanches.Electrical.Geometry.BoundaryMidpoints
public import FiniteAvalanches.Electrical.Energy

/-! Consumption of the proved packing and edge-copy charging bounds. -/
@[expose] public section

namespace FiniteAvalanches.Electrical.Geometry
open scoped BigOperators Classical

theorem dirichlet_energy_le_log {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (Q : E → Square) (q : V → Option E)
    (M epsilon y0 lambda d : ℝ) (he : 0 < epsilon) (hl : 1 ≤ lambda) (hd : 0 ≤ d)
    (f weight : V → ℝ) (p : V → ℝ × ℝ) (z t : E → ℝ × ℝ) (bad : Finset E)
    (hf : ∀ e ∈ bad, 0 ≤ f (a e) ∧ f (a e) ≤ 1 ∧ 0 ≤ f (b e) ∧ f (b e) ≤ 1)
    (hw : ∀ v, 0 ≤ weight v ∧ weight v ≤ 1)
    (hq : ∀ v e, q v = some e → v = a e ∨ v = b e)
    (hdeg : ∀ v, q v ≠ none → degree a b v ≤ d)
    (hz : ∀ e, e ∉ bad → weight (a e)*weight (b e) ≠ 0 →
      z e ∈ ((Q e).dilate lambda (by linarith)).carrier ∧
      t e ∈ ((Q e).dilate lambda (by linarith)).carrier)
    (ha : ∀ e, e ∉ bad → weight (a e)*weight (b e) ≠ 0 →
      endpointFits Q q epsilon y0 lambda hl f p (a e) (z e))
    (hb : ∀ e, e ∉ bad → weight (a e)*weight (b e) ≠ 0 →
      endpointFits Q q epsilon y0 lambda hl f p (b e) (t e))
    (hM : 0 ≤ M) (heM : epsilon ≤ min 1 M)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set E) (fun e => (Q e).openCarrier))
    (hQ : ∀ e, (Q e).carrier ⊆ rectangle 0 1 0 M) :
    FiniteAvalanches.Electrical.weightedEnergy a b weight f ≤
      (bad.card : ℝ) + 3*(1+2*d)*64*(4*lambda^2)^2 *
        (3 + Real.log (min 1 M/epsilon)/Real.log 2) := by
  unfold FiniteAvalanches.Electrical.weightedEnergy
  have hc := dirichlet_charging_le a b Q q epsilon y0 lambda d he hl hd f weight p z t bad hf hw hq hdeg hz ha hb
  have hp := angular_energy_le_log Finset.univ Q (by simpa using hdisj)
    M epsilon y0 lambda hM he heM hl (fun e _ => hQ e)
  have hcoef : 0 ≤ 3*(1+2*d) := by positivity
  calc
    _ ≤ (bad.card : ℝ) + 3*(1+2*d)*∑ e, ((Q e).angularOsc epsilon y0 lambda hl he)^2 := hc
    _ ≤ (bad.card : ℝ) + 3*(1+2*d)*(64*(4*lambda^2)^2 *
        (3 + Real.log (min 1 M/epsilon)/Real.log 2)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hcoef)
    _ = _ := by ring

end FiniteAvalanches.Electrical.Geometry
