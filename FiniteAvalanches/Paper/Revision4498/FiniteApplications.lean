import FiniteAvalanches.Paper.SectionThreeOrigin.InverseWaves
import FiniteAvalanches.Sandpile.Waves.ReciprocalBound
import FiniteAvalanches.Sandpile.Waves.BurnedSet
import FiniteAvalanches.Sandpile.Components.TreeMass
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths
import FiniteAvalanches.Sandpile.Source.RadiusCutPast

/-! Finite wave and tree-past applications for the revised manuscript. -/

set_option autoImplicit false
namespace FiniteAvalanches.Paper.Revised
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open FiniteAvalanches.Sandpile.SourceCounting (origin)
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Trees.Lattice.PastTail
open FiniteAvalanches.Sandpile.Source
open scoped Classical BigOperators ENNReal
noncomputable section

/-- The wave started at `h` topples precisely the core of its forward output. -/
theorem wave_counts_eq_core_forward {N : ℕ} (h : Punctured N (origin N)) :
    ∀ x : Site2, waveCounts h.val x = if x ∈ core (forward h).val then 1 else 0 :=
  (SectionThreeOrigin.inverse_waves_origin h).1

/-- The forward transition count has the original tree-count normalization. -/
theorem outflow_card_le_treeCount_mul_reciprocal {N : ℕ}
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site (origin N)) (nbrFinset (FiniteWired.site (origin N))) ⊆
      markedSites S) :
    (Nat.card {g : Punctured N (origin N) //
      markedSites S ⊆ core g.val ∧ ¬markedSites S ⊆ core (forward g).val} : ℝ) ≤
      (WiredTrees.treeCount N : ℝ) *
        ∫ t, WiredTrees.reciprocal N (markedVertices S)
          (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
          ∂WiredTrees.law N := by
  have h := normalized_inverse_transitions_le_reciprocal (origin N) S hN
  have hswap :
      (∑ h : Punctured N (origin N),
        (if ¬markedSites S ⊆ core h.val ∧ markedSites S ⊆ core (inverse h).val
          then 1 else 0 : ℝ)) =
      ∑ g : Punctured N (origin N),
        (if markedSites S ⊆ core g.val ∧ ¬markedSites S ⊆ core (forward g).val
          then 1 else 0 : ℝ) := by
    with_reducible convert sum_inverse_transitions_eq_forward (origin N) (markedSites S) using 1
    all_goals
      refine Finset.sum_congr ?_ ?_
      · ext g
        simp only [Finset.mem_univ]
      · intro g _
        split_ifs <;> rfl
  have hforward :
      (∑ g : Punctured N (origin N),
        (if markedSites S ⊆ core g.val ∧ ¬markedSites S ⊆ core (forward g).val
          then 1 else 0 : ℝ)) / Fintype.card (FiniteWired.Recurrent N) ≤
      ∫ t, WiredTrees.reciprocal N (markedVertices S)
        (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
        ∂WiredTrees.law N := by
    rw [← hswap]
    with_reducible convert h using 1
  have hcard :
      (∑ g : Punctured N (origin N),
        (if markedSites S ⊆ core g.val ∧ ¬markedSites S ⊆ core (forward g).val
          then 1 else 0 : ℝ)) =
      (Nat.card {g : Punctured N (origin N) //
        markedSites S ⊆ core g.val ∧ ¬markedSites S ⊆ core (forward g).val} : ℝ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact Finset.sum_boole _ _
  rw [hcard] at hforward
  have hden : (0 : ℝ) < Fintype.card (FiniteWired.Recurrent N) := by
    exact_mod_cast Fintype.card_pos
  have hraw := (div_le_iff₀ hden).mp hforward
  rw [card_original_recurrent_eq_treeCount] at hraw
  simpa only [mul_comm] using hraw

/-- The past of a vertex in `B_r` leaves `B_M` only if it leaves its own
square of radius `M-r`. -/
theorem past_outside_origin_box_subset {r M : ℕ} {x : Site2}
    (hx : x ∈ boxSites r) :
    {ω : EdgeField | ∃ hT : IsTree ω, ∃ hOne : OneEnded ω,
      ¬vertexPast ω hT hOne x ⊆ (boxSites M : Set Site2)} ⊆
      pastEscapesSup x ((M : ℝ) - (r : ℝ)) := by
  rintro ω ⟨hT, hOne, hout⟩
  apply (mem_pastEscapesSup_iff ω hT hOne x _).mpr
  intro h
  exact hout (h.trans (supBall_subset_box hx))

/-- The origin-box formulation uses the same universal constant as the
centered past estimate. -/
theorem past_outside_origin_box_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r M : ℕ, r + 2 ≤ M → ∀ x : Site2,
      x ∈ boxSites r →
      (squareLatticeUST : Measure EdgeField).real
        {ω | ∃ hT : IsTree ω, ∃ hOne : OneEnded ω,
          ¬vertexPast ω hT hOne x ⊆ (boxSites M : Set Site2)} ≤
        C * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C, hC, htail⟩ := vertex_past_tail
  refine ⟨C, hC, ?_⟩
  intro r M hM x hx
  have hgap : 2 ≤ (M : ℝ) - (r : ℝ) := by
    exact_mod_cast (show (2 : ℤ) ≤ (M : ℤ) - (r : ℤ) by omega)
  exact (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (past_outside_origin_box_subset hx))).trans (htail x _ hgap)

end
end FiniteAvalanches.Paper.Revised
