import FiniteAvalanches.Wilson.Lattice.SiteRootForests
import FiniteAvalanches.Trees.ForestProjection.Dpp
import FiniteAvalanches.External.LyonsProjectionDomination

/-! Lattice edge laws of uniform rooted forests of wired boxes with roots the sink and
the sites outside a fixed set `Γ`, recording the lattice edges with both endpoints in `Γ`.
The law does not depend on the box once `Γ` lies in it, on a box itself it is the wired
uniform spanning tree law of that box, and enlarging `Γ` increases the probability of
every event requiring a finite set of edges to be present (Lyons's domination of nested
projection determinantal processes). -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.SiteRoots

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open scoped Classical ENNReal

noncomputable section

theorem graph_reaches (N : ℕ) : ∀ x y, (WiredTrees.graph N).reaches Finset.univ x y := by
  intro x y
  exact (WiredTrees.graph N).reaches_mono (Finset.subset_univ _)
    ((WiredTrees.rowTree N).property.2.2.1 x (Set.mem_univ x) y (Set.mem_univ y))

instance forestNonempty (Γ : Set (Site 2)) (N : ℕ) : Nonempty (Forest Γ N) :=
  (WiredTrees.graph N).nonempty_rootedForest _ ⟨none, trivial⟩ (graph_reaches N)

instance forestMeasurableSpace (Γ : Set (Site 2)) (N : ℕ) : MeasurableSpace (Forest Γ N) := ⊤

instance forestMeasurableSingletonClass (Γ : Set (Site 2)) (N : ℕ) :
    MeasurableSingletonClass (Forest Γ N) := ⟨fun _ => trivial⟩

/-- The lattice edges with both endpoints in `Γ` carried by a set of box copies. -/
def forestField (Γ : Set (Site 2)) {N : ℕ} (F : Finset (FiniteWired.Edge N)) : EdgeField :=
  fun e => decide (∃ c ∈ F, TreeMeasurability11.originalCopyEdge c = e ∧ ∀ z ∈ e.val, z ∈ Γ)

theorem forestField_eq_true (Γ : Set (Site 2)) {N : ℕ} (F : Finset (FiniteWired.Edge N))
    (e : LatticeEdge) :
    forestField Γ F e = true ↔
      ∃ c ∈ F, TreeMeasurability11.originalCopyEdge c = e ∧ ∀ z ∈ e.val, z ∈ Γ := by
  simp only [forestField, decide_eq_true_eq]

theorem forestField_image_copyInLarger (Γ : Set (Site 2)) {N M : ℕ} (hNM : N ≤ M)
    (F : Finset (FiniteWired.Edge N)) :
    forestField Γ (F.image (copyInLarger hNM)) = forestField Γ F := by
  funext e
  apply Bool.eq_iff_iff.mpr
  rw [forestField_eq_true, forestField_eq_true]
  constructor
  · rintro ⟨c, hc, hce, hz⟩
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨d, hd, (copyInLarger_original hNM d).symm.trans hce, hz⟩
  · rintro ⟨d, hd, hde, hz⟩
    exact ⟨copyInLarger hNM d, Finset.mem_image_of_mem _ hd,
      (copyInLarger_original hNM d).trans hde, hz⟩

/-- The lattice edge law of uniform rooted forests with roots the sink and `Γᶜ`. -/
def forestLaw (Γ : Set (Site 2)) (N : ℕ) : Measure EdgeField :=
  Measure.map (fun F : Forest Γ N => forestField Γ F.val)
    (FiniteAvalanches.uniformMeasure (Forest Γ N))

instance forestLaw_probability (Γ : Set (Site 2)) (N : ℕ) : IsProbabilityMeasure (forestLaw Γ N) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem forestLaw_apply (Γ : Set (Site 2)) (N : ℕ) (A : Set EdgeField) (hA : MeasurableSet A) :
    forestLaw Γ N A =
      (Nat.card {F : Forest Γ N // forestField Γ F.val ∈ A} : ℝ≥0∞) / Nat.card (Forest Γ N) := by
  rw [forestLaw, Measure.map_apply (measurable_of_countable _) hA,
    FiniteAvalanches.uniformMeasure_apply]
  rfl

/-- The law does not depend on the box once `Γ` lies in the smaller box. -/
theorem forestLaw_eq_of_le (Γ : Set (Site 2)) {N M : ℕ} (hNM : N ≤ M)
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) : forestLaw Γ N = forestLaw Γ M := by
  have hmap : (fun F : Forest Γ M => forestField Γ F.val) ∘ forestEquiv hNM Γ hΓ =
      fun F : Forest Γ N => forestField Γ F.val := by
    funext F
    simp only [Function.comp_apply, forestEquiv_copies, forestField_image_copyInLarger]
  rw [forestLaw, forestLaw, ← hmap, ← Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _), FiniteAvalanches.uniform_measure_map_equiv]

/-- The real probability of a copy-set event is the sum of the rooted forest masses. -/
theorem forestLaw_toReal_eq_sum (Γ : Set (Site 2)) (N : ℕ) (A : Set EdgeField)
    (hA : MeasurableSet A) :
    (forestLaw Γ N A).toReal =
      ∑ F : Finset (FiniteWired.Edge N), Set.indicator {F | forestField Γ F ∈ A}
        ((WiredTrees.graph N).uniformRootedForestMass (roots Γ N).val ⟨none, trivial⟩
          (graph_reaches N)) F := by
  rw [(WiredTrees.graph N).sum_uniformRootedForestMass_event, forestLaw_apply Γ N A hA,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  rfl

/-- The event that every edge of a finite set is present. -/
def allPresent (Fl : Finset LatticeEdge) : Set EdgeField := {ω | ∀ e ∈ Fl, ω e = true}

theorem measurableSet_allPresent (Fl : Finset LatticeEdge) : MeasurableSet (allPresent Fl) := by
  have h : allPresent Fl = ⋂ e ∈ Fl, {ω : EdgeField | ω e = true} := by
    ext ω
    simp [allPresent]
  rw [h]
  exact Finset.measurableSet_biInter _ fun e _ =>
    (measurableSet_singleton true).preimage (measurable_pi_apply e)

/-- Enlarging `Γ` increases the probability that a finite set of edges inside `Γ` is
present. -/
theorem forestLaw_allPresent_mono {Γ Γ' : Set (Site 2)} (hΓΓ' : Γ ⊆ Γ') (N : ℕ)
    (Fl : Finset LatticeEdge) (hFl : ∀ e ∈ Fl, ∀ z ∈ e.val, z ∈ Γ) :
    forestLaw Γ N (allPresent Fl) ≤ forestLaw Γ' N (allPresent Fl) := by
  let G := WiredTrees.graph N
  let ev : Set (Finset (FiniteWired.Edge N)) :=
    {F | ∀ e ∈ Fl, ∃ c ∈ F, TreeMeasurability11.originalCopyEdge c = e}
  have hev : ∀ (S : Set (Site 2)), (∀ e ∈ Fl, ∀ z ∈ e.val, z ∈ S) →
      {F : Finset (FiniteWired.Edge N) | forestField S F ∈ allPresent Fl} = ev := by
    intro S hS
    ext F
    simp only [Set.mem_setOf_eq, allPresent, forestField_eq_true, ev]
    exact forall₂_congr fun e he =>
      ⟨fun ⟨c, hc, hce, _⟩ => ⟨c, hc, hce⟩, fun ⟨c, hc, hce⟩ => ⟨c, hc, hce, hS e he⟩⟩
  have hinc : ∀ F ∈ ev, ∀ e, insert e F ∈ ev := by
    intro F hF e f hf
    obtain ⟨c, hc, hce⟩ := hF f hf
    exact ⟨c, Finset.mem_insert_of_mem hc, hce⟩
  have hroots : (roots Γ' N).val ⊆ (roots Γ N).val := by
    intro v hv
    cases v with
    | none => trivial
    | some x => exact fun h => hv (hΓΓ' h)
  have hconn := graph_reaches N
  have hc := G.supportGraph_preconnected_of_reaches hconn
  have hR : (roots Γ N).val.Nonempty := ⟨none, trivial⟩
  have hR' : (roots Γ' N).val.Nonempty := ⟨none, trivial⟩
  have hle := G.range_rootProjection_antitone (Set.toFinset_subset_toFinset.mpr hroots)
    (Set.toFinset_nonempty.mpr hR') (Set.toFinset_nonempty.mpr hR) hc
  have hd := FiniteAvalanches.External.lyons_nestedProjectionDomination
    (G.rootProjection (roots Γ N).val.toFinset (Set.toFinset_nonempty.mpr hR) hc)
    (G.rootProjection (roots Γ' N).val.toFinset (Set.toFinset_nonempty.mpr hR') hc)
    (G.rootProjection_transpose _ (Set.toFinset_nonempty.mpr hR) hc)
    (G.rootProjection_idempotent _ (Set.toFinset_nonempty.mpr hR) hc)
    (G.rootProjection_transpose _ (Set.toFinset_nonempty.mpr hR') hc)
    (G.rootProjection_idempotent _ (Set.toFinset_nonempty.mpr hR') hc)
    hle
    (G.uniformRootedForestMass (roots Γ N).val hR hconn)
    (G.uniformRootedForestMass (roots Γ' N).val hR' hconn)
    (G.uniformRootedForestMass_nonneg _ hR hconn)
    (G.uniformRootedForestMass_nonneg _ hR' hconn)
    (G.uniformRootedForestMass_set_inclusion_det _ hR hconn)
    (G.uniformRootedForestMass_set_inclusion_det _ hR' hconn)
  have h := hd.1 ev hinc
  have hl := forestLaw_toReal_eq_sum Γ N (allPresent Fl) (measurableSet_allPresent Fl)
  have hr := forestLaw_toReal_eq_sum Γ' N (allPresent Fl) (measurableSet_allPresent Fl)
  rw [hev Γ hFl] at hl
  rw [hev Γ' (fun e he z hz => hΓΓ' (hFl e he z hz))] at hr
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _), hl, hr]
  exact h

end

end FiniteAvalanches.Wilson.Lattice.SiteRoots
