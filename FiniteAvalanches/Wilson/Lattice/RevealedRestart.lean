import FiniteAvalanches.Wilson.Lattice.RestartGeometry

/-! An internal application of a universal revealed-root bound to actual histories. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.ActualRevealedRestart
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open BatchRestart ActualRestartGeometry
open scoped Classical
noncomputable section

/-- The universal revealed-root input is consumed after deriving all root
containments from the complete stopped histories. -/
theorem internal_restarted_contact_bound_of_revealed_estimate (ε : ℝ)
    (hrevealed : ∃ κ : ℕ, 30 ≤ κ ∧
      ∀ (K : Finset (Site 2)) (γ : SimpleRay),
        ((lattice 2).induce (K : Set (Site 2))).Connected →
        0 ∈ K → Disjoint (K : Set (Site 2)) γ.vertices →
        (lattice 2).Adj 0 (γ.vertex 0) →
        ∀ (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
        16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
        ∀ (R : RootPair), (K : Set (Site 2)) ⊆ R.zero →
          R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
          γ.vertices ⊆ R.one →
          ε / 2 ≤ (wilsonColorLaw R).real
            (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ)))) :
    ∃ κ : ℕ, 30 ≤ κ ∧
      ∀ (K : Finset (Site 2)) (γ : SimpleRay)
        (hK : ((lattice 2).induce (K : Set (Site 2))).Connected) (h0 : 0 ∈ K)
        (hd : Disjoint (K : Set (Site 2)) γ.vertices)
        (ha : (lattice 2).Adj 0 (γ.vertex 0))
        (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
        16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
        ∀ (L : List (Site 2)) (ξ : ℕ → WalkDriver) (out : SamplerState)
          (hs : samplerRun (initialSampler
            (prependConnectingPair K hK γ 0 h0 ha
              (fun n hn => Set.disjoint_left.mp hd hn ⟨n, rfl⟩)).roots) L ξ = some out),
          (∀ p ∈ out.history, ∀ j : Fin (p.length + 1),
            p.vertex j ∈ (boxSites h : Set (Site 2))) →
          let R := (prependConnectingPair K hK γ 0 h0 ha
            (fun n hn => Set.disjoint_left.mp hd hn ⟨n, rfl⟩)).roots
          ε / 2 ≤ (wilsonColorLaw (restartedRoots R L ξ out hs)).real
            (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ))) := by
  obtain ⟨κ, hκ, hbound⟩ := hrevealed
  refine ⟨κ, hκ, ?_⟩
  intro K γ hK h0 hd ha h r hh hr hdiam L ξ out hs hstay
  obtain ⟨hzero, hbox, hone⟩ := disjoint_ray_restarted_geometry
    K γ hK h0 hd ha L ξ out hs h hstay
  exact hbound K γ hK h0 hd ha h r hh hr hdiam _ hzero hbox hone

end
end FiniteAvalanches.Wilson.Lattice.ActualRevealedRestart
