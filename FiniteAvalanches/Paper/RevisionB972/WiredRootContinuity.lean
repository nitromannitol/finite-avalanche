import FiniteAvalanches.Paper.Revision4498.ColorContinuity

set_option autoImplicit false
namespace FiniteAvalanches.Paper.RevisionB972
open LatticeProb MeasureTheory Filter FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- Literal zero roots in the source's closed square box. -/
def wiredZeroSites (R : RootPair) (N : ℕ) : Set (Site 2) :=
  R.zero ∩ {x | FiniteWired.inBox N x}

/-- Literal one roots: the original roots inside the box and every outside site. -/
def wiredOneSites (R : RootPair) (N : ℕ) : Set (Site 2) :=
  (R.one ∩ {x | FiniteWired.inBox N x}) ∪ {x | ¬FiniteWired.inBox N x}

/-- The actual wired pair on its valid source domain. The numerical condition is
internal to root formation and is discharged eventually below. -/
def wiredRootPair (R : RootPair) (N : ℕ) (hN : (wiredZeroSites R N).Nonempty) :
    RootPair where
  zero := wiredZeroSites R N
  one := wiredOneSites R N
  disjoint := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hy with hy | hy
    · exact Set.disjoint_left.mp R.disjoint hx.1 hy.1
    · exact hy hx.2
  zero_nonempty := hN
  one_nonempty := by
    obtain ⟨x, hx⟩ := R.one_nonempty
    by_cases hbox : FiniteWired.inBox N x
    · exact ⟨x, Or.inl ⟨hx, hbox⟩⟩
    · exact ⟨x, Or.inr hbox⟩

theorem wiredZeroSites_eventually_nonempty (R : RootPair) :
    ∀ᶠ N : ℕ in atTop, (wiredZeroSites R N).Nonempty := by
  obtain ⟨a, ha⟩ := R.zero_nonempty
  filter_upwards [eventually_inBox a] with N hN
  exact ⟨a, ha, hN⟩

/-- Finite-prefix adapter only. At indices where the source has no zero root,
use the valid limit pair. Eventually the pair is literally the source's wired pair. -/
def wiredPrefixCompletion (R : RootPair) (N : ℕ) : RootPair :=
  if hN : (wiredZeroSites R N).Nonempty then wiredRootPair R N hN else R

theorem wiredPrefixCompletion_eventually_exact (R : RootPair) :
    ∀ᶠ N : ℕ in atTop,
      (wiredPrefixCompletion R N).zero = wiredZeroSites R N ∧
      (wiredPrefixCompletion R N).one = wiredOneSites R N := by
  filter_upwards [wiredZeroSites_eventually_nonempty R] with N hN
  rw [wiredPrefixCompletion, dif_pos hN]
  exact ⟨rfl, rfl⟩

theorem wiredPrefixCompletion_local_zero (R : RootPair) (x : Site 2) :
    ∀ᶠ N : ℕ in atTop, x ∈ (wiredPrefixCompletion R N).zero ↔ x ∈ R.zero := by
  filter_upwards [wiredZeroSites_eventually_nonempty R, eventually_inBox x] with N hN hx
  rw [wiredPrefixCompletion, dif_pos hN]
  change (x ∈ R.zero ∧ FiniteWired.inBox N x) ↔ x ∈ R.zero
  exact ⟨And.left, fun h => ⟨h, hx⟩⟩

theorem wiredPrefixCompletion_local_one (R : RootPair) (x : Site 2) :
    ∀ᶠ N : ℕ in atTop, x ∈ (wiredPrefixCompletion R N).one ↔ x ∈ R.one := by
  filter_upwards [wiredZeroSites_eventually_nonempty R, eventually_inBox x] with N hN hx
  rw [wiredPrefixCompletion, dif_pos hN]
  change ((x ∈ R.one ∧ FiniteWired.inBox N x) ∨ ¬FiniteWired.inBox N x) ↔ x ∈ R.one
  constructor
  · rintro (h | h)
    · exact h.1
    · exact False.elim (h hx)
  · intro h
    exact Or.inl ⟨h, hx⟩

/-- Every finite joint color pattern for the concrete wired family converges.
No root formation, local-agreement or convergence hypothesis is added. -/
theorem wired_color_cylinder_tendsto (R : RootPair)
    (F : Finset (Site 2)) (p : F → Bool) :
    Tendsto (fun N => wilsonColorLaw (wiredPrefixCompletion R N) (colorCylinder F p))
      atTop (nhds (wilsonColorLaw R (colorCylinder F p))) := by
  exact FiniteAvalanches.Paper.Revision4498.color_cylinder_tendsto
    (wiredPrefixCompletion R) R (wiredPrefixCompletion_local_zero R)
    (wiredPrefixCompletion_local_one R) F p

end
end FiniteAvalanches.Paper.RevisionB972
