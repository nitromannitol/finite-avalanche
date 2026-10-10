import FiniteAvalanches.Trees.AmbientContactCount
import FiniteAvalanches.Trees.Lattice.FiniteObservationForestLaw
import FiniteAvalanches.Trees.Lattice.OriginalContactCount
import FiniteAvalanches.Trees.ForestProjection.ColorEvents

/-! The single-volume dictionary uses every ambient original copy and every
lattice neighbor, including the distinct exits of a boundary vertex. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.WiredTrees
open FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

/-- The literal lattice sites of the active vertices in a wired vertex set. -/
def activeSites (N : ℕ) (A : Set (FiniteWired.Vertex N)) : Finset (Site 2) :=
  (Finset.univ.filter (fun x : FiniteWired.Active N => some x ∈ A)).image FiniteWired.site

theorem site_mem_activeSites (N : ℕ) (A : Set (FiniteWired.Vertex N))
    (x : FiniteWired.Active N) :
    FiniteWired.site x ∈ activeSites N A ↔ some x ∈ A := by
  simp only [activeSites, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (FiniteWired.site_injective N he) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem activeSites_inBox (N : ℕ) (A : Set (FiniteWired.Vertex N))
    {z : Site 2} (hz : z ∈ activeSites N A) : FiniteWired.inBox N z := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  exact fun i => (x i).property

theorem activeLift_activeSites (N : ℕ) (A : Set (FiniteWired.Vertex N))
    (hsink : none ∉ A) : activeLift N (activeSites N A : Set (Site 2)) = A := by
  ext v
  cases v with
  | none =>
    simp only [sink_not_mem_activeLift]
    exact (iff_false_intro hsink).symm
  | some x =>
    rw [some_mem_activeLift]
    exact site_mem_activeSites N A x

/-- Exactly the zero sites of an actual finite rooted forest. -/
def forestZeroSites (R : RootPair) (N : ℕ) (F : FiniteForest R N) : Finset (Site 2) :=
  activeSites N {v | finiteColors R N F v = false}

theorem finiteColors_true_iff_oneVertices (R : RootPair) (N : ℕ)
    (F : FiniteForest R N) (v : FiniteWired.Vertex N) :
    finiteColors R N F v = true ↔ v ∈ (graph N).oneVertices F.val (wiredOne R N) := by
  simp only [finiteColors, decide_eq_true_eq, Multigraph.oneVertices, Set.mem_setOf_eq]

theorem forestZeroSites_activeLift (R : RootPair) (N : ℕ) (F : FiniteForest R N) :
    activeLift N (forestZeroSites R N F : Set (Site 2)) =
      (graph N).oneVertices F.val (wiredZero R N) := by
  have hsink : none ∉ ({v | finiteColors R N F v = false} : Set (FiniteWired.Vertex N)) := by
    change finiteColors R N F none ≠ false
    rw [finiteColors_one R N F (v := none) trivial]
    exact Bool.noConfusion
  rw [forestZeroSites, activeLift_activeSites N _ hsink]
  have hc := (graph N).oneVertices_eq_compl_zeroVertices
    (wiredZero R N) (wiredOne R N) (wired_roots_disjoint R N) F
  ext v
  change finiteColors R N F v = false ↔ v ∈ (graph N).oneVertices F.val (wiredZero R N)
  rw [← Bool.eq_false_eq_not_eq_true, finiteColors_true_iff_oneVertices, hc]
  exact not_not

theorem finiteForestField_complement_zeroSites (R : RootPair) (N : ℕ)
    (F : FiniteForest R N) :
    (finiteForestField R N F).2 = fun y => decide (y ∉ forestZeroSites R N F) := by
  funext y
  by_cases hy : FiniteWired.inBox N y
  · let x := FiniteWired.activeOfSite N y hy
    have hx : FiniteWired.site x = y := rfl
    have hm : y ∈ forestZeroSites R N F ↔ finiteColors R N F (some x) = false := by
      rw [← hx]
      exact site_mem_activeSites N _ x
    change finiteColors R N F (wiredSite N y) = _
    rw [wiredSite, dif_pos hy]
    cases hcol : finiteColors R N F (some x) <;> simp only [hcol, Bool.true_eq_false, iff_false, iff_true] at hm
    · simp only [hm, not_true_eq_false, decide_false]
    · simp only [hm, not_false_eq_true, decide_true]
  · have hm : y ∉ forestZeroSites R N F := fun hm => hy (activeSites_inBox N _ hm)
    rw [finiteForestField_outside R N F hy, decide_eq_true hm]

/-- No copied count equality is assumed: roots force K to be zero, and the
complementary finite component supplies the original-contact helper's premises. -/
theorem finite_forest_ambient_contacts (R : RootPair) (N : ℕ)
    (K : Finset (Site 2)) (hK : activeLift N (K : Set (Site 2)) ⊆ wiredZero R N)
    (hbox : ∀ z ∈ K, FiniteWired.inBox N z) (F : FiniteForest R N) :
    ambientColorContacts (graph N) (activeLift N (K : Set (Site 2)))
      (wiredOne R N) F.val = contacts K (finiteForestField R N F).2 := by
  have hKC : K ⊆ forestZeroSites R N F := by
    intro z hz
    let x := FiniteWired.activeOfSite N z (hbox z hz)
    have hx : some x ∈ wiredZero R N := hK ((some_mem_activeLift N _ x).mpr hz)
    exact (site_mem_activeSites N _ x).mpr (finiteColors_zero R N F hx)
  have hc := (graph N).oneVertices_eq_compl_zeroVertices
    (wiredZero R N) (wiredOne R N) (wired_roots_disjoint R N) F
  have hsub : activeLift N (K : Set (Site 2)) ⊆
      activeLift N (forestZeroSites R N F : Set (Site 2)) := by
    rintro _ ⟨x, rfl, hx⟩
    exact (some_mem_activeLift N _ x).mpr (hKC hx)
  have hcolor : (graph N).oneVertices F.val (wiredOne R N) =
      (activeLift N (forestZeroSites R N F : Set (Site 2)))ᶜ := by
    rw [forestZeroSites_activeLift]
    exact hc
  calc
    ambientColorContacts (graph N) (activeLift N (K : Set (Site 2)))
        (wiredOne R N) F.val =
        ((graph N).admissibleEdges (activeLift N (forestZeroSites R N F : Set (Site 2)))
          (activeLift N (K : Set (Site 2)))).card :=
      ambientColorContacts_eq_admissible (graph N) _ _ _ F.val hsub hcolor
    _ = contacts K (fun y => decide (y ∉ forestZeroSites R N F)) :=
      ReciprocalCertificate14.original_contact_count N K (forestZeroSites R N F)
        hKC (fun z hz => activeSites_inBox N _ hz)
    _ = contacts K (finiteForestField R N F).2 := by
      rw [finiteForestField_complement_zeroSites]

/-- Every actual forest for the observation's actual roots has the literal
all-ambient-copy statistic equal to the lattice contact statistic. -/
theorem observation_forest_contact_count (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none S hS ≠ none)
    (F : FiniteForest (observationRootPair N S hS t₀ hne₀) N) :
    ambientColorContacts (graph N) ((graph N).span t₀ S)
      (wiredOne (observationRootPair N S hS t₀ hne₀) N) F.val =
      contacts (activeSites N ((graph N).span t₀ S))
        (finiteForestField (observationRootPair N S hS t₀ hne₀) N F).2 := by
  have hk := activeLift_activeSites N ((graph N).span t₀ S)
    (sink_not_mem_observed_span N S hS t₀ hne₀)
  have hz : activeLift N (activeSites N ((graph N).span t₀ S) : Set (Site 2)) ⊆
      wiredZero (observationRootPair N S hS t₀ hne₀) N := by
    rw [hk, observationRootPair_wiredZero]
  have he := finite_forest_ambient_contacts (observationRootPair N S hS t₀ hne₀) N
    (activeSites N ((graph N).span t₀ S)) hz (fun z hz => activeSites_inBox N _ hz) F
  rw [hk] at he
  exact he

end
end FiniteAvalanches.ConditioningConsumer
