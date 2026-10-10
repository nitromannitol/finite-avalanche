import FiniteAvalanches.Wilson.Lattice.CofiniteRestartGeometry
import FiniteAvalanches.Wilson.Lattice.ContactHistory

/-! One-step conditional contact mass for the literal connected cofinite source. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CofiniteHistorySuccess
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open BatchRestart ConditionalIteration7 ActualContactHistory CofiniteRestartGeometry
open scoped Classical
noncomputable section

/-- The next box queries both endpoints of every original incidence in the window. -/
theorem source_and_contact_endpoints_queried (K : Finset (Site 2)) (r : ℕ) :
    let F := K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ))
    ∀ d ∈ F ∪ contactSites F, d ∈ (boxSites (3 * r + 1)).toList := by
  dsimp only
  intro d hd
  apply Finset.mem_toList.mpr
  rcases Finset.mem_union.mp hd with hsource | hneighbor
  · have hr : siteRadius 0 d ≤ 3 * r := by
      exact_mod_cast (Finset.mem_filter.mp hsource).2
    apply box_sites_mono (Nat.le_succ (3 * r))
    rw [mem_box_sites]
    intro i
    have hi := (siteRadius_le_iff 0 d (3 * r)).mp hr i
    simp only [Pi.zero_apply, sub_zero] at hi
    exact abs_le.mp hi
  · exact contact_endpoints_subset_box K r hneighbor

/-- A confined successful prefix consumes the joint estimate at its actual restarted roots. -/
theorem one_step_history_success_of_open_joint_v3
    (hjoint : (∃ ε : ℝ, 0 < ε ∧
  (∀ (r : ℕ), 10 ^ 30 ≤ r → ∀ (R : RootPair),
    (R.zero ∪ R.one)ᶜ.Finite →
    0 ∈ R.zero →
    (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
    ((lattice 2).induce R.zero).Connected →
    (∃ x ∈ R.zero, 2 * r ≤ siteRadius 0 x) →
    ((lattice 2).induce R.one).Connected →
    (∃ y ∈ R.one, siteRadius 0 y = r) →
    ε ≤ (wilsonColorLaw R).real
      (localContactEvent R.zero 0 (2 * r) ((1 / 8 : ℝ) * Real.log (r : ℝ)))) ∧
  (∃ κ : ℕ, 30 ≤ κ ∧
    ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      0 ∈ K → Disjoint (K : Set (Site 2)) γ →
      ((lattice 2).induce γ).Connected → γᶜ.Finite →
      (∃ b ∈ γ, (lattice 2).Adj 0 b) →
      ∀ (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
      16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ (R : RootPair), (K : Set (Site 2)) ⊆ R.zero →
        R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
        γ ⊆ R.one →
        ε / 2 ≤ (wilsonColorLaw R).real
          (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ)))))) :
    ∃ ε : ℝ, 0 < ε ∧
  (∀ (r : ℕ), 10 ^ 30 ≤ r → ∀ (R : RootPair),
    (R.zero ∪ R.one)ᶜ.Finite →
    0 ∈ R.zero →
    (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
    ((lattice 2).induce R.zero).Connected →
    (∃ x ∈ R.zero, 2 * r ≤ siteRadius 0 x) →
    ((lattice 2).induce R.one).Connected →
    (∃ y ∈ R.one, siteRadius 0 y = r) →
    ε ≤ (wilsonColorLaw R).real
      (localContactEvent R.zero 0 (2 * r) ((1 / 8 : ℝ) * Real.log (r : ℝ)))) ∧
      ∃ κ : ℕ, 30 ≤ κ ∧
        ∀ (K : Finset (Site 2)) (γ : Set (Site 2))
          (_hK : ((lattice 2).induce (K : Set (Site 2))).Connected)
          (h0 : (0 : Site 2) ∈ K) (hd : Disjoint (K : Set (Site 2)) γ)
          (_hconn : ((lattice 2).induce γ).Connected) (_hfinite : γᶜ.Finite)
          (hb : ∃ b ∈ γ, (lattice 2).Adj 0 b)
          (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
          16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
          ∀ (L : List (Site 2)) (ξ : Rows) (out : SamplerState)
            (_hs : samplerRun (initialSampler (sourceRoots K γ hd h0 hb)) L ξ = some out),
            (∀ p ∈ out.history, ∀ j : Fin (p.length + 1),
              p.vertex j ∈ (boxSites h : Set (Site 2))) →
            let R := sourceRoots K γ hd h0 hb
            let F := K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ))
            (ε / 2) * wilsonRows.real (historyAtom R L out) ≤
              wilsonRows.real (historyAtom R L out ∩
                continuationContactEvent (initialSampler R)
                  (L ++ (boxSites (3 * r + 1)).toList) F
                  ((1 / 16 : ℝ) * Real.log (r : ℝ))) := by
  obtain ⟨ε, hε, hlocal, κ, hκ, hrevealed⟩ := hjoint
  refine ⟨ε, hε, hlocal, κ, hκ, ?_⟩
  intro K γ hK h0 hd hconn hfinite hb h r hh hr hdiam L ξ out hs hstay
  obtain ⟨_, _, hKconn, hγconn, _, _, hzero, hneighbor⟩ :=
    source_roots_geometry K γ hK h0 hd hconn hfinite hb
  obtain ⟨hKsub, hbox, hγsub, _, _⟩ :=
    source_restarted_geometry K γ h0 hd hfinite hb L ξ out hs h hstay
  have hmass := hrevealed K γ hKconn hzero hd hγconn hfinite hneighbor
    h r hh hr hdiam (restartedRoots (sourceRoots K γ hd h0 hb) L ξ out hs)
    hKsub hbox hγsub
  exact (mul_le_mul_of_nonneg_right hmass (measureReal_nonneg)).trans
    (history_contact_success_mass (sourceRoots K γ hd h0 hb) L
      (boxSites (3 * r + 1)).toList ξ out hs
      (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ)))
      ((1 / 16 : ℝ) * Real.log (r : ℝ))
      (fun d hd' => source_and_contact_endpoints_queried K r d
        (Finset.mem_union.mpr (Or.inr hd'))))

end
end FiniteAvalanches.Wilson.Lattice.CofiniteHistorySuccess
