import FiniteAvalanches.Wilson.Lattice.WiredObservationConvergence

/-! Clopen joint cylinders of the finite wired forest fields. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Finite joint edge and color observations are clopen in the product field. -/
theorem isClopen_jointEvent (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) : IsClopen (jointEvent E D pe pc) := by
  have he : IsClopen (⋂ e ∈ E, {ω : ForestField | ω.1 e = pe e}) :=
    isClopen_biInter_finset fun e _ =>
      (isClopen_discrete {pe e}).preimage ((continuous_apply e).comp continuous_fst)
  have hd : IsClopen (⋂ z ∈ D, {ω : ForestField | ω.2 z = pc z}) :=
    isClopen_biInter_finset fun z _ =>
      (isClopen_discrete {pc z}).preimage ((continuous_apply z).comp continuous_snd)
  have hs : jointEvent E D pe pc =
      (⋂ e ∈ E, {ω : ForestField | ω.1 e = pe e}) ∩
      (⋂ z ∈ D, {ω : ForestField | ω.2 z = pc z}) := by
    ext ω
    simp only [jointEvent, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hs]
  exact he.inter hd

/-- Finite wired field probabilities agree with the corresponding original
copy-forest observation probabilities. -/
theorem finiteForestLaw_jointEvent (R : RootPair) (B : ℕ) (E : Finset LatticeEdge)
    (D : Finset (Site 2)) (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) :
    finiteForestLaw R B (jointEvent E D pe pc) =
      finiteUniformLaw R B (wiredObservationCylinder R B E D pe pc) := by
  rw [finiteForestLaw, Measure.map_apply (finiteForestField_measurable R B)
    (isClopen_jointEvent E D pe pc).isClosed.measurableSet]
  congr 1

/-- The finite wired joint field probabilities converge to the corresponding
finite recurrent Wilson query probabilities. -/
theorem finiteForestLaw_jointEvent_tendsto (R : RootPair) (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hD : ∀ z ∈ D, ∃ i < n, x i = z) :
    Tendsto (fun B => finiteForestLaw R B (jointEvent E D pe pc)) atTop
      (nhds (wilsonRows (samplerEvent R ((List.range n).map x) E D pe pc))) := by
  have ht := finiteUniformLaw_wiredObservationCylinder_tendsto R x ka kb n E D pe pc hE hD
  have he : (fun B => finiteForestLaw R B (jointEvent E D pe pc)) =
      (fun B => finiteUniformLaw R B (wiredObservationCylinder R B E D pe pc)) := by
    funext B
    exact finiteForestLaw_jointEvent R B E D pe pc
  rw [he]
  exact ht

end
end FiniteAvalanches.Wilson.Lattice
