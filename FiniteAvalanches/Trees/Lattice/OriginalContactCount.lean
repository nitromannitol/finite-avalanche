import FiniteAvalanches.Trees.Lattice.WiredCutComponents
import FiniteAvalanches.Trees.Lattice.TreeContinuityObjects
import FiniteAvalanches.Sandpile.Components.Directions

set_option autoImplicit false
open scoped Classical
noncomputable section
namespace ReciprocalCertificate14
open LatticeProb FiniteAvalanches FiniteAvalanches.Trees
open FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Components
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice

private theorem crossing_direction_iff {N : ℕ} (C : Finset (Site 2))
    (hbox : ∀ z ∈ C, FiniteWired.inBox N z) (x : FiniteWired.Active N)
    (hx : FiniteWired.site x ∈ C) (d : FiniteWired.Direction) :
    FiniteWired.directionEdge x d ∈ (WiredTrees.graph N).crossingAt
      (activeLift N C) (some x) ↔ FiniteWired.site x + FiniteWired.step d ∉ C := by
  rcases d with ⟨i,b⟩
  cases b
  all_goals simp only [FiniteWired.directionEdge]
  all_goals split_ifs with hb
  all_goals simp only [Multigraph.crossingAt, Finset.mem_filter, Finset.mem_univ,
    true_and, WiredTrees.graph, Multigraph.ofEndpoints, FiniteWired.endpoints,
    some_mem_activeLift, Finset.mem_coe, FiniteWired.site_activeOfSite,
    Option.some.injEq, sink_not_mem_activeLift, hx, true_and,
    FiniteWired.step, Bool.false_eq_true, if_false, if_true, ← sub_eq_add_neg]
  · have hn : FiniteWired.activeOfSite N (FiniteWired.site x - unit i) hb ≠ x := by
      intro h
      have he := congrArg FiniteWired.site h
      have hi := congrFun he i
      simp only [FiniteWired.site_activeOfSite, Pi.sub_apply, unit, Pi.single_eq_same] at hi
      omega
    simp [hn]
  · have hn : FiniteWired.site x - unit i ∉ C := fun h => hb (hbox _ h)
    simp [hn]
  · have hn : FiniteWired.activeOfSite N (FiniteWired.site x + unit i) hb ≠ x := by
      intro h
      have he := congrArg FiniteWired.site h
      have hi := congrFun he i
      simp only [FiniteWired.site_activeOfSite, Pi.add_apply, unit, Pi.single_eq_same] at hi
      omega
    simp [hn]
  · have hn : FiniteWired.site x + unit i ∉ C := fun h => hb (hbox _ h)
    simp [hn]

private theorem crossing_card_directions {N : ℕ} (C : Finset (Site 2))
    (hbox : ∀ z ∈ C, FiniteWired.inBox N z) (x : FiniteWired.Active N)
    (hx : FiniteWired.site x ∈ C) :
    ((WiredTrees.graph N).crossingAt (activeLift N C) (some x)).card =
      (outerDirections C (FiniteWired.site x)).card := by
  have he : (WiredTrees.graph N).crossingAt (activeLift N C) (some x) =
      (outerDirections C (FiniteWired.site x)).image (FiniteWired.directionEdge x) := by
    ext e
    constructor
    · intro he
      have hi : incident x e := by
        simp only [Multigraph.crossingAt, Finset.mem_filter, Finset.mem_univ, true_and] at he
        have h := he.2
        exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
      obtain ⟨d, rfl⟩ := exists_direction_of_incident x e hi
      exact Finset.mem_image.mpr ⟨d, by
        simpa only [outerDirections, Finset.mem_filter, Finset.mem_univ, true_and]
          using (crossing_direction_iff C hbox x hx d).mp he, rfl⟩
    · rintro he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      apply (crossing_direction_iff C hbox x hx d).mpr
      exact (Finset.mem_filter.mp hd).2
  rw [he, Finset.card_image_of_injective _ (direction_edge_injective x)]

private theorem neighbor_sum_directions (C : Finset (Site 2)) (x : Site 2) :
    (∑ y ∈ nbrFinset x, if decide (y ∉ C) then 1 else 0) =
      (outerDirections C x).card := by
  have hinj : Function.Injective (fun d : FiniteWired.Direction => x + FiniteWired.step d) :=
    fun _ _ h => FiniteWired.step_injective (add_left_cancel h)
  have he : (Finset.univ : Finset FiniteWired.Direction).image
      (fun d => x + FiniteWired.step d) = nbrFinset x := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, nbrFinset,
      Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨i,b⟩, rfl⟩
      cases b
      · exact ⟨i, Or.inr (by simp [FiniteWired.step, sub_eq_add_neg])⟩
      · exact ⟨i, Or.inl (by simp [FiniteWired.step])⟩
    · rintro ⟨i, hi | hi⟩
      · exact ⟨(i,true), by simpa [FiniteWired.step] using hi.symm⟩
      · exact ⟨(i,false), by simpa [FiniteWired.step, ← sub_eq_add_neg] using hi.symm⟩
  rw [← he, Finset.sum_image (fun a _ b _ h => hinj h)]
  simp only [outerDirections, Finset.card_eq_sum_ones, Finset.sum_filter,
    decide_eq_true_eq]

/-- Literal original wired-copy contacts equal the full original lattice-neighbor
count. No selected-edge filter occurs, and separate sink exits are retained. -/
theorem original_contact_count (N : ℕ) (K C : Finset (Site 2)) (hKC : K ⊆ C)
    (hbox : ∀ z ∈ C, FiniteWired.inBox N z) :
    ((WiredTrees.graph N).admissibleEdges (activeLift N C) (activeLift N K)).card =
      contacts K (fun y => decide (y ∉ C)) := by
  have hsub : activeLift N (K : Set (Site 2)) ⊆ activeLift N C := by
    rintro _ ⟨x,rfl,hx⟩
    exact (some_mem_activeLift _ _ _).mpr (hKC hx)
  rw [(WiredTrees.graph N).card_admissibleEdges _ _ hsub]
  let f : {z : Site 2 // z ∈ K} → FiniteWired.Vertex N :=
    fun z => some (FiniteWired.activeOfSite N z.val (hbox _ (hKC z.property)))
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg FiniteWired.site (Option.some.inj h)
  have he : (activeLift N (K : Set (Site 2))).toFinset = K.attach.image f := by
    ext v
    simp only [Set.mem_toFinset, activeLift, Set.mem_setOf_eq, Finset.mem_image,
      Finset.mem_attach, true_and]
    constructor
    · rintro ⟨x,rfl,hx⟩
      refine ⟨⟨FiniteWired.site x,hx⟩, ?_⟩
      exact congrArg some (FiniteWired.site_injective N rfl)
    · rintro ⟨z,rfl⟩
      exact ⟨FiniteWired.activeOfSite N z.val (hbox _ (hKC z.property)), rfl, z.property⟩
  rw [he, Finset.sum_image (fun a _ b _ h => hf h)]
  change (∑ z ∈ K.attach, ((WiredTrees.graph N).crossingAt (activeLift N C)
    (some (FiniteWired.activeOfSite N z.val (hbox _ (hKC z.property))))).card) = _
  trans ∑ z ∈ K.attach, (outerDirections C z.val).card
  · apply Finset.sum_congr rfl
    intro z _
    exact crossing_card_directions C hbox _ (hKC z.property)
  rw [Finset.sum_attach K (fun z : Site 2 => (outerDirections C z).card)]
  unfold contacts
  exact Finset.sum_congr rfl (fun x _ => (neighbor_sum_directions C x).symm)

#print axioms original_contact_count
end ReciprocalCertificate14
