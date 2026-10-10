import FiniteAvalanches.Wilson.Lattice.LocalComparison.NeedleGeometry

set_option autoImplicit false
namespace JointElectricalSymmetry
open FiniteAvalanches.Electrical FiniteAvalanches.Needle
open FiniteAvalanches.Sandpile.FiniteWired
open FiniteAvalanches (siteRadius)
open scoped Classical BigOperators
noncomputable section

theorem energy_complement {V E : Type*} [Fintype E] (a b : E → V) (f : V → ℝ) :
    energy a b (fun x => 1-f x) = energy a b f := by
  unfold energy
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- The actual annulus with the local comparison's inner-one, exterior-zero orientation. -/
theorem local_annulus_trial (r : ℕ) (hr : 1 ≤ r) :
    let N := 2*r-1
    let S := Finset.univ.filter (fun x : Active N => siteRadius 0 (site x) ≤ r)
    let f := fun x : Vertex N => 1-voltage N S x
    f none = 0 ∧ (∀ x ∈ S, f (some x) = 1) ∧
      energy (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2) f ≤ 16 := by
  dsimp only
  have hs := voltage_spec (2*r-1)
    (Finset.univ.filter (fun x : Active (2*r-1) => siteRadius 0 (site x) ≤ r))
  refine ⟨by rw [hs.1]; ring, ?_, ?_⟩
  · intro x hx
    rw [hs.2.1 x hx]
    ring
  · rw [energy_complement]
    exact JointNeedleGeometry.annulus_sixteen r hr

end
end JointElectricalSymmetry
