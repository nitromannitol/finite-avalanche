import FiniteAvalanches.Wilson.Lattice.TranslationExpectation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual conditional consumer of translation covariance at the opening of the
ct:reciprocal:v2 proof. The universal origin estimate remains an open antecedent;
no manuscript estimate or frozen source statement is claimed proved here. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.Translation.Consumer
open LatticeProb MeasureTheory
open scoped Classical
noncomputable section

/-- For any selected adjacent source vertex, the actual root law, complete
contact expectation and diameter survive normalization to the origin. -/
theorem normalize_adjacent_geometry (K : Finset (Site 2)) (γ : SimpleRay)
    (hconn : ((lattice 2).induce (K : Set (Site 2))).Connected)
    (hdisj : Disjoint (K : Set (Site 2)) γ.vertices) (k : Site 2) (hk : k ∈ K)
    (hadj : (lattice 2).Adj k (γ.vertex 0)) (R : RootPair)
    (h0 : R.zero = (K : Set (Site 2))) (h1 : R.one = γ.vertices) :
    ((lattice 2).induce (finiteSet K (-k) : Set (Site 2))).Connected ∧
    Disjoint (finiteSet K (-k) : Set (Site 2)) (ray γ (-k)).vertices ∧
    0 ∈ finiteSet K (-k) ∧
    (lattice 2).Adj 0 ((ray γ (-k)).vertex 0) ∧
    (roots R (-k)).zero = (finiteSet K (-k) : Set (Site 2)) ∧
    (roots R (-k)).one = (ray γ (-k)).vertices ∧
    (wilsonColorLaw R).map (colors (-k)) = wilsonColorLaw (roots R (-k)) ∧
    (∫ σ, (1 : ℝ) / (contacts (finiteSet K (-k)) σ : ℝ) ∂wilsonColorLaw (roots R (-k))) =
      (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ∧
    (finiteSet K (-k)).sup (fun x => (finiteSet K (-k)).sup (fun y => FiniteAvalanches.siteRadius x y)) =
      K.sup (fun x => K.sup (fun y => FiniteAvalanches.siteRadius x y)) := by
  obtain ⟨hmem, hneighbor⟩ := origin_geometry K γ k hk hadj
  exact ⟨connected_translate K (-k) hconn, disjoint_translate K γ (-k) hdisj,
    hmem, hneighbor, roots_zero R K (-k) h0, roots_one R γ (-k) h1,
    wilsonColorLaw_map R (-k), reciprocal_expectation_translate R K (-k),
    diameter_translate K (-k)⟩

/-- A universal origin estimate suffices for the exact arbitrary adjacent-root
reciprocal conclusion, with precisely the SAME exponent and constant. This is a
logical implication consuming the actual normalization, not an estimate proof. -/
theorem arbitrary_reciprocal_of_origin (a C : ℝ)
    (hOrigin : ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected → 0 ∈ K →
      ∀ γ : SimpleRay, Disjoint (K : Set (Site 2)) γ.vertices →
        (lattice 2).Adj 0 (γ.vertex 0) →
        ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ.vertices →
          (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
            C * Real.rpow (Real.log
              (((K.sup (fun x => K.sup (fun y => FiniteAvalanches.siteRadius x y)) : ℕ) : ℝ) + 2)) (-a)) :
    ∀ K : Finset (Site 2), ((lattice 2).induce (K : Set (Site 2))).Connected →
      ∀ γ : SimpleRay, Disjoint (K : Set (Site 2)) γ.vertices →
        (∃ k ∈ K, (lattice 2).Adj k (γ.vertex 0)) →
        ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ.vertices →
          (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
            C * Real.rpow (Real.log
              (((K.sup (fun x => K.sup (fun y => FiniteAvalanches.siteRadius x y)) : ℕ) : ℝ) + 2)) (-a) := by
  intro K hconn γ hdisj hadj R h0 h1
  obtain ⟨k, hk, hneighbor⟩ := hadj
  obtain ⟨hc, hd, hmem, ha, hr0, hr1, _, he, hdiam⟩ :=
    normalize_adjacent_geometry K γ hconn hdisj k hk hneighbor R h0 h1
  have hbound := hOrigin (finiteSet K (-k)) hc hmem (ray γ (-k)) hd ha
    (roots R (-k)) hr0 hr1
  rw [he, hdiam] at hbound
  exact hbound

end
end FiniteAvalanches.Wilson.Lattice.Translation.Consumer
