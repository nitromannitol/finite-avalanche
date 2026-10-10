import FiniteAvalanches.Sandpile.Waves.OrderedSupports
import FiniteAvalanches.Sandpile.Components.CutSites
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! All actual complete-avalanche waves are counted with their edge boundaries.
The root-path equality is a full finite copied-carrier reindexing, not a sampled-wave law. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- Every original copied edge with exactly one endpoint in the active support. -/
def boundaryCopies {N : ℕ} (W : Finset Site2) : Finset (FiniteWired.Edge N) :=
  Finset.univ.filter ((WiredTrees.graph N).crosses {v | insideVertex W v})

theorem mem_boundaryCopies {N : ℕ} (W : Finset Site2) (e : FiniteWired.Edge N) :
    e ∈ boundaryCopies W ↔ (WiredTrees.graph N).crosses {v | insideVertex W v} e := by
  simp only [boundaryCopies, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Original active cut sites recover the entire original core, with no endpoint quotient. -/
theorem cutSites_crossing_core {N : ℕ} (o : FiniteWired.Active N) (e : FiniteWired.Edge N)
    (g : {g : Punctured N o // (WiredTrees.graph N).crosses
      (insideSupport (coreShape g.val)) e}) :
    cutSites o (crossingCoreTreeEquiv o e g).val e = core g.val.val := by
  have hs := crossing_core_component o e g
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hc : some x ∈ (WiredTrees.graph N).componentAfter
        (crossingCoreTreeEquiv o e g).val.val e (some o) := (Finset.mem_filter.mp hx).2
    rw [hs] at hc
    exact hc
  · intro hz
    let x := FiniteWired.activeOfSite N z
      ((mem_box_sites N z).mp ((coreShape g.val.val).property.1 hz))
    change FiniteWired.site x ∈ cutSites o (crossingCoreTreeEquiv o e g).val e
    rw [mem_cutSites]
    change some x ∈ (WiredTrees.graph N).componentAfter
      (crossingCoreTreeEquiv o e g).val.val e (some o)
    rw [hs]
    exact hz

/-- Fixed-copy insertion transports arbitrary finite shape weights, including infinite values. -/
theorem sum_crossing_core_eq_tree_cut {M : Type*} [AddCommMonoid M] {N : ℕ}
    (o : FiniteWired.Active N) (e : FiniteWired.Edge N) (Φ : Finset Site2 → M) :
    (∑ g : Punctured N o, if e ∈ boundaryCopies (core g.val) then Φ (core g.val) else 0) =
    ∑ t : (WiredTrees.graph N).SpanningTree,
      if e ∈ (WiredTrees.graph N).rootPathCopies t (some o) none then Φ (cutSites o t e) else 0 := by
  let C : Set (Punctured N o) :=
    {g | (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) e}
  let T : Set (WiredTrees.graph N).SpanningTree :=
    {t | e ∈ t.val ∧ ¬(WiredTrees.graph N).reaches (t.val.erase e) (some o) none}
  calc
    _ = ∑ g : C, Φ (core g.val.val) := by
      apply Finset.sum_congr_set C
      · intro g hg
        exact if_pos ((mem_boundaryCopies _ _).mpr hg)
      · intro g hg
        exact if_neg (fun h => hg ((mem_boundaryCopies _ _).mp h))
    _ = ∑ t : T, Φ (cutSites o t.val e) := by
      have he := (crossingCoreTreeEquiv o e).sum_comp
        (fun t => Φ (cutSites o t.val e))
      have hh : (∑ g : C, Φ (core g.val.val)) =
          ∑ g : C, Φ (cutSites o (crossingCoreTreeEquiv o e g).val e) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [cutSites_crossing_core]
      exact hh.trans he
    _ = _ := by
      symm
      apply Finset.sum_congr_set T
      · intro t ht
        exact if_pos (((WiredTrees.graph N).mem_rootPathCopies t (some o) none e).mpr ht)
      · intro t ht
        exact if_neg (fun h => ht (((WiredTrees.graph N).mem_rootPathCopies t (some o) none e).mp h))

end
end FiniteAvalanches.Sandpile.Components

namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- Sum the shape weight over EVERY actual wave whose original edge boundary contains e. -/
def finiteBoundaryWaveSum {M : Type*} [AddCommMonoid M] {N : ℕ}
    (o : FiniteWired.Active N) (e : FiniteWired.Edge N) (Φ : Finset Site2 → M)
    (η : FiniteWired.Recurrent N) : M :=
  finiteWaveSum o (fun W => if e ∈ boundaryCopies W then Φ W else 0) η

/-- A whole-carrier finite weighted sum, before either side is normalized. -/
theorem sum_finite_boundary_waves {M : Type*} [AddCommMonoid M] {N : ℕ}
    (o : FiniteWired.Active N) (e : FiniteWired.Edge N) (Φ : Finset Site2 → M) :
    (∑ η : FiniteWired.Recurrent N, finiteBoundaryWaveSum o e Φ η) =
    ∑ t : (WiredTrees.graph N).SpanningTree,
      if e ∈ (WiredTrees.graph N).rootPathCopies t (some o) none then Φ (cutSites o t e) else 0 := by
  change (∑ η : FiniteWired.Recurrent N,
    finiteWaveSum o (fun W => if e ∈ boundaryCopies W then Φ W else 0) η) = _
  rw [sum_finite_wave_sum]
  exact sum_crossing_core_eq_tree_cut o e Φ

/-- The finite original recurrent-law expectation equals the actual uniform-tree weighted cut event. -/
theorem integral_finite_boundary_waves {N : ℕ} (o : FiniteWired.Active N)
    (e : FiniteWired.Edge N) (Φ : Finset Site2 → ℝ) :
    (∫ η, finiteBoundaryWaveSum o e Φ η ∂FiniteWired.law N) =
    ∫ t, (if e ∈ (WiredTrees.graph N).rootPathCopies t (some o) none
      then Φ (cutSites o t e) else 0) ∂WiredTrees.law N := by
  have hl : FiniteWired.law N = uniformMeasure (FiniteWired.Recurrent N) := by
    simp only [FiniteWired.law, uniformMeasure, Nat.card_eq_fintype_card]
  rw [hl, integral_uniformMeasure]
  change _ = ∫ t, _ ∂uniformMeasure (WiredTrees.graph N).SpanningTree
  rw [integral_uniformMeasure, sum_finite_boundary_waves]
  have hd : Nat.card (FiniteWired.Recurrent N) = Nat.card (WiredTrees.graph N).SpanningTree :=
    Nat.card_congr (originalRecurrentTreeEquiv N)
  rw [hd]

/-- No boundedness is required: arbitrary nonnegative extended weights retain the same common mass. -/
theorem lintegral_finite_boundary_waves {N : ℕ} (o : FiniteWired.Active N)
    (e : FiniteWired.Edge N) (Φ : Finset Site2 → ℝ≥0∞) :
    (∫⁻ η, finiteBoundaryWaveSum o e Φ η ∂FiniteWired.law N) =
    ∫⁻ t, (if e ∈ (WiredTrees.graph N).rootPathCopies t (some o) none
      then Φ (cutSites o t e) else 0) ∂WiredTrees.law N := by
  have hl : FiniteWired.law N = uniformMeasure (FiniteWired.Recurrent N) := by
    simp only [FiniteWired.law, uniformMeasure, Nat.card_eq_fintype_card]
  rw [hl]
  change _ = ∫⁻ t, _ ∂uniformMeasure (WiredTrees.graph N).SpanningTree
  simp only [uniformMeasure, lintegral_smul_measure, smul_eq_mul, lintegral_count,
    tsum_fintype, sum_finite_boundary_waves]
  rw [Nat.card_congr (originalRecurrentTreeEquiv N)]

end
end FiniteAvalanches.Sandpile.Waves
