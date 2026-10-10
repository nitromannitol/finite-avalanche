import FiniteAvalanches.Wilson.Lattice.ReciprocalStepThreeGeometry
import FiniteAvalanches.Wilson.Lattice.ReciprocalStepThreeScalar
import FiniteAvalanches.Wilson.Lattice.StoppedHistoryLocalization
import FiniteAvalanches.Sandpile.LocalConfinement
import FiniteAvalanches.Sandpile.WiredTermination

/-! The reciprocal proof's square-batch escape estimate for actual full histories. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.ReciprocalStepThree
open LatticeProb MeasureTheory FiniteAvalanches.Sandpile
open scoped Classical ENNReal
noncomputable section

/-- The query is exactly the source closed square, with every site queried once. -/
theorem query_list_length (r : ℕ) :
    (boxSites (3 * r + 1)).toList.length = (6 * r + 3) ^ 2 := by
  rw [Finset.length_toList, card_box_sites]
  congr 1
  omega

/-- One universal positive constant bounds escapes in actual successful recorded
walks, including their terminal endpoint. The connected obstacle and diameter
supply all geometric hypotheses of the installed localization theorem. -/
theorem reciprocal_step_three_history_escape : ∃ D : ℝ, 0 < D ∧
    ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected → (0 : Site 2) ∈ K →
    ∀ R : RootPair, (K : Set (Site 2)) ⊆ R.zero →
    ∀ r : ℕ, 2 ≤ r →
      16 * r ^ 6 ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      wilsonRows {ξ : ℕ → WalkDriver | ∃ out,
        samplerRun (initialSampler R) (boxSites (3 * r + 1)).toList ξ = some out ∧
        ∃ p ∈ out.history, ∃ j : Fin (p.length + 1),
          r ^ 6 < siteRadius 0 (p.vertex j)} ≤
        ENNReal.ofReal (D * (r : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨D, hD, hbound⟩ :=
    StoppedHistoryLocalization.finite_stopped_history_localization_bound
  refine ⟨128 * D, mul_pos (by norm_num) hD, ?_⟩
  intro K hK h0 R hKR r hr hdiam
  have hmargin := sixth_power_margin r hr
  have hboundary : ∃ z ∈ K, siteRadius 0 z = r ^ 6 - 1 :=
    connected_boundary_of_diameter K hK.preconnected h0 (r ^ 6 - 1)
      (by omega) (by omega)
  have hqueries : ∀ x ∈ (boxSites (3 * r + 1)).toList,
      siteRadius 0 x ≤ 3 * r + 1 := by
    intro x hx
    exact (site_radius_zero_le_iff x _).mpr (Finset.mem_toList.mp hx)
  have hb := hbound (K : Set (Site 2)) hK.preconnected h0 R hKR
    (3 * r + 1) (r ^ 6) hmargin hboundary
    (boxSites (3 * r + 1)).toList hqueries
  have hs := query_sixth_power_bound_mul D (r : ℝ) hD.le (by exact_mod_cast hr)
  have hs' : (((boxSites (3 * r + 1)).toList.length : ℝ) * D *
      Real.sqrt ((((3 * r + 1 + 1 : ℕ) : ℝ)) / (r ^ 6 : ℕ))) ≤
      (128 * D) * (r : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [query_list_length]
    push_cast
    rw [show (3 : ℝ) * r + 1 + 1 = 3 * r + 2 by ring]
    exact hs
  exact hb.trans (ENNReal.ofReal_le_ofReal hs')

end
end FiniteAvalanches.Wilson.Lattice.ReciprocalStepThree
