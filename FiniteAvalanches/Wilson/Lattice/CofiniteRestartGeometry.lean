import FiniteAvalanches.Wilson.Lattice.RestartGeometry
import FiniteAvalanches.Sandpile.LocalConfinement

/-! Literal cofinite source roots and their terminal-inclusive restarted geometry. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CofiniteRestartGeometry
open LatticeProb FiniteAvalanches Sandpile BatchRestart ActualRestartGeometry
open scoped Classical
noncomputable section

/-- The original zero and one roots are exactly the two prescribed source sets. -/
def sourceRoots (K : Finset (Site 2)) (γ : Set (Site 2))
    (hd : Disjoint (K : Set (Site 2)) γ) (h0 : (0 : Site 2) ∈ K)
    (hb : ∃ b ∈ γ, (lattice 2).Adj 0 b) : RootPair where
  zero := K
  one := γ
  disjoint := hd
  zero_nonempty := ⟨0, h0⟩
  one_nonempty := by
    obtain ⟨b, hmem, _⟩ := hb
    exact ⟨b, hmem⟩

/-- Containing a cofinite set supplies the finite-complement domain. -/
theorem compl_finite_of_contains (γ A : Set (Site 2))
    (hγ : γᶜ.Finite) (hA : γ ⊆ A) : Aᶜ.Finite :=
  hγ.subset (fun _ hx hy => hx (hA hy))

/-- The source premises supply all initial root geometry without additional fields. -/
theorem source_roots_geometry (K : Finset (Site 2)) (γ : Set (Site 2))
    (hK : ((lattice 2).induce (K : Set (Site 2))).Connected)
    (h0 : (0 : Site 2) ∈ K) (hd : Disjoint (K : Set (Site 2)) γ)
    (hconn : ((lattice 2).induce γ).Connected) (hfinite : γᶜ.Finite)
    (hb : ∃ b ∈ γ, (lattice 2).Adj 0 b) :
    let R := sourceRoots K γ hd h0 hb
    R.zero.Nonempty ∧ R.one.Nonempty ∧
      ((lattice 2).induce R.zero).Connected ∧
      ((lattice 2).induce R.one).Connected ∧
      R.oneᶜ.Finite ∧ (R.zero ∪ R.one)ᶜ.Finite ∧
      (0 : Site 2) ∈ R.zero ∧ (∃ b ∈ R.one, (lattice 2).Adj 0 b) := by
  exact ⟨⟨0, h0⟩, (sourceRoots K γ hd h0 hb).one_nonempty, hK, hconn, hfinite,
    compl_finite_of_contains γ ((K : Set (Site 2)) ∪ γ) hfinite
      (fun _ hx => Or.inr hx), h0, hb⟩

/-- Complete recorded paths include their hit vertex; confinement bounds all new roots. -/
theorem source_restarted_geometry (K : Finset (Site 2)) (γ : Set (Site 2))
    (h0 : (0 : Site 2) ∈ K) (hd : Disjoint (K : Set (Site 2)) γ)
    (hfinite : γᶜ.Finite) (hb : ∃ b ∈ γ, (lattice 2).Adj 0 b)
    (L : List (Site 2)) (ξ : ℕ → WalkDriver) (out : SamplerState)
    (hs : samplerRun (initialSampler (sourceRoots K γ hd h0 hb)) L ξ = some out)
    (h : ℕ) (hstay : ∀ p ∈ out.history, ∀ j : Fin (p.length + 1),
      p.vertex j ∈ (boxSites h : Set (Site 2))) :
    let R := restartedRoots (sourceRoots K γ hd h0 hb) L ξ out hs
    (K : Set (Site 2)) ⊆ R.zero ∧
      R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) ∧
      γ ⊆ R.one ∧ R.oneᶜ.Finite ∧ (R.zero ∪ R.one)ᶜ.Finite := by
  have hroots := original_roots_subset_restarted (sourceRoots K γ hd h0 hb) L ξ out hs
  have hbox := restarted_zero_subset_of_history (sourceRoots K γ hd h0 hb)
    L ξ out hs h hstay
  exact ⟨hroots.1, hbox, hroots.2,
    compl_finite_of_contains γ _ hfinite hroots.2,
    compl_finite_of_contains γ _ hfinite (fun _ hx => Or.inr (hroots.2 hx))⟩

/-- Every endpoint used by the original contact count lies in the queried next box. -/
theorem contact_endpoints_subset_box (K : Finset (Site 2)) (r : ℕ) :
    contactSites (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ))) ⊆
      boxSites (3 * r + 1) := by
  intro y hy
  obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
  have hr : siteRadius 0 x ≤ 3 * r := by
    exact_mod_cast (Finset.mem_filter.mp hx).2
  have hxbox : x ∈ boxSites (3 * r) := by
    rw [mem_box_sites]
    intro i
    have hi := (siteRadius_le_iff 0 x (3 * r)).mp hr i
    simp only [Pi.zero_apply, sub_zero] at hi
    exact abs_le.mp hi
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton] at hy
  obtain ⟨j, rfl | rfl⟩ := hy
  · exact box_sites_add_unit hxbox j
  · exact box_sites_sub_unit hxbox j

end
end FiniteAvalanches.Wilson.Lattice.CofiniteRestartGeometry
