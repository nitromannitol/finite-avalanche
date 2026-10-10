import FiniteAvalanches.Wilson.Lattice.CofiniteClosedContact
import FiniteAvalanches.Wilson.Lattice.CofiniteExploration

/-! Full actual source consumption, with universal constants and arbitrary literal roots. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CofiniteClosedContactConsumer
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open CofiniteRestartGeometry CofiniteClosedContact
open scoped Classical
noncomputable section

/-- The actual two-root law is independent of the proof fields used to package the sets. -/
theorem roots_eq_source (R : RootPair) (K : Finset (Site 2)) (γ : Set (Site 2))
    (hd : Disjoint (K : Set (Site 2)) γ) (h0 : (0 : Site 2) ∈ K)
    (hb : ∃ b ∈ γ, (lattice 2).Adj 0 b)
    (hzero : R.zero = (K : Set (Site 2))) (hone : R.one = γ) :
    R = sourceRoots K γ hd h0 hb := by
  cases R
  cases hzero
  cases hone
  rfl

/-- Consume the source bound at the actual nu_(K,gamma), with no success,
iteration, sampler-termination, scale, or localization inputs. -/
theorem actual_source_global_closed_tail_of_open_joint_v3
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
      ∃ κ : ℕ, 30 ≤ κ ∧ ∃ D : ℝ, 0 < D ∧
        ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
          ((lattice 2).induce (K : Set (Site 2))).Connected →
          (0 : Site 2) ∈ K → Disjoint (K : Set (Site 2)) γ →
          ((lattice 2).induce γ).Connected → γᶜ.Finite →
          (∃ b ∈ γ, (lattice 2).Adj 0 b) →
          ∀ (R : RootPair), R.zero = (K : Set (Site 2)) → R.one = γ →
          ∀ n : ℕ, 1 ≤ n →
            16 * ((2 : ℝ) ^ ((6 * κ) ^ (2 * n - 1))) ≤
              ((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) →
            (wilsonColorLaw R).real
              {σ : ColorField | (contacts K σ : ℝ) ≤
                (1 / 16 : ℝ) * Real.log ((2 : ℝ) ^ ((6 * κ) ^ n))} ≤
              (1 - ε / 2) ^ n +
                2 * D * ((2 : ℝ) ^ ((6 * κ) ^ (n - 1))) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨ε, hε, hlocal, κ, hκ, D, hD, hglobal⟩ :=
    actual_cofinite_global_closed_tail_of_open_joint_v3 hjoint
  refine ⟨ε, hε, hlocal, κ, hκ, D, hD, ?_⟩
  intro K γ hK h0 hd hconn hfinite hb R hzero hone n hn hdiam
  rw [roots_eq_source R K γ hd h0 hb hzero hone]
  have hdiamnat : 16 * 2 ^ ((6 * κ) ^ (2 * n - 1)) ≤
      K.sup (fun x => K.sup (fun y => siteRadius x y)) := by exact_mod_cast hdiam
  have hm := hglobal K γ hK h0 hd hconn hfinite hb n hn hdiamnat
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hm

end
end FiniteAvalanches.Wilson.Lattice.CofiniteClosedContactConsumer
