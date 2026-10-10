module

public import FiniteAvalanches.Sandpile.Burning.InducedGraph

@[expose] public section

/-! Subset degrees, not only total degrees, are transported to the actual copied
graphs. This is the degree information needed for forbidden subconfigurations. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E)

omit [Fintype V] in
theorem subtype_mem_image_iff (C : Finset V) (S : Finset (InducedVertex C))
    (v : InducedVertex C) : v ∈ S ↔ v.val ∈ S.image Subtype.val := by
  constructor
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  · intro hv
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hv
    have he' : w = v := Subtype.ext he
    exact he' ▸ hw

omit [Fintype V] in
theorem project_vertex_mem_image_iff (A : Finset V) (S : Finset (InducedVertex A)) (v : V) :
    projectVertex A v ∈ S.image some ↔ v ∈ S.image Subtype.val := by
  constructor
  · intro hv
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hv
    have he' := (project_vertex_eq_some_iff A v w).mp he.symm
    exact Finset.mem_image.mpr ⟨w, hw, he'.symm⟩
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨w, hw, ((project_vertex_eq_some_iff A w.val w).mpr rfl).symm⟩

theorem degree_into_induced_graph (C : Finset V) (S : Finset (InducedVertex C))
    (v : InducedVertex C) :
    degreeInto (inducedGraph G C) S v = degreeInto G (S.image Subtype.val) v.val := by
  unfold degreeInto incidentInto
  simp only [inducedGraph, Subtype.ext_iff, subtype_mem_image_iff]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he
  · intro a _ b _ h
    exact Subtype.ext h
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hr
      have hrC : G.right e ∈ C := hew ▸ w.property
      refine ⟨⟨e, hl ▸ v.property, hrC⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        (Or.inl ⟨hl, Finset.mem_image.mpr ⟨w, hw, hew⟩⟩)
    · obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hl
      have hlC : G.left e ∈ C := hew ▸ w.property
      refine ⟨⟨e, hlC, hr ▸ v.property⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        (Or.inr ⟨hr, Finset.mem_image.mpr ⟨w, hw, hew⟩⟩)

theorem degree_into_held_graph (s : V) (A B : Finset V) (hs : s ∉ A)
    (hBA : B ⊆ A) (S : Finset (InducedVertex A)) (v : InducedVertex A) :
    degreeInto (heldGraph G s A B hs hBA) (S.image some) (some v) =
      degreeInto G (S.image Subtype.val) v.val := by
  unfold degreeInto incidentInto
  simp only [heldGraph, project_vertex_eq_some_iff, project_vertex_mem_image_iff]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he
  · intro a _ b _ h
    exact Subtype.ext h
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hr
      have hrA : G.right e ∈ A := hew ▸ w.property
      have hret : retained G A B e := Or.inl ⟨hl ▸ v.property, hrA⟩
      refine ⟨⟨e, hret⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        (Or.inl ⟨hl, Finset.mem_image.mpr ⟨w, hw, hew⟩⟩)
    · obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hl
      have hlA : G.left e ∈ A := hew ▸ w.property
      have hret : retained G A B e := Or.inl ⟨hlA, hr ▸ v.property⟩
      refine ⟨⟨e, hret⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        (Or.inr ⟨hr, Finset.mem_image.mpr ⟨w, hw, hew⟩⟩)

/-- Exact transport of every stable height, with no excluded degree-zero vertex. -/
def inducedHeightsEquiv (C : Finset V) :
    ((v : InducedVertex C) → Fin (degree (inducedGraph G C) v)) ≃
      ((v : InducedVertex C) → Fin (degreeInto G C v.val)) :=
  Equiv.piCongrRight fun v => Equiv.cast (congrArg Fin (degree_induced_graph G C v))

/-- Held vertices retain original degree; unheld vertices use the internal degree. -/
def heldHeightsEquiv (s : V) (A B : Finset V) (hs : s ∉ A) (hBA : B ⊆ A) :
    ((v : InducedVertex A) → Fin (degree (heldGraph G s A B hs hBA) (some v))) ≃
      ((v : InducedVertex A) → Fin
        (if v.val ∈ B then degree G v.val else degreeInto G A v.val)) :=
  Equiv.piCongrRight fun v => Equiv.cast (congrArg Fin (degree_held_graph G s A B hs hBA v))

end
end FiniteAvalanches.Sandpile.Burning
