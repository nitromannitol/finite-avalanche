module

public import FiniteAvalanches.Sandpile.Burning.Degrees

@[expose] public section

                                                                             
                                                                               
                                                                          
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E)

abbrev InducedVertex (C : Finset V) := {v : V // v ∈ C}
abbrev InducedEdge (C : Finset V) := {e : E // G.left e ∈ C ∧ G.right e ∈ C}

def inducedGraph (C : Finset V) : Multigraph (InducedVertex C) (InducedEdge G C) where
  left e := ⟨G.left e.val, e.property.1⟩
  right e := ⟨G.right e.val, e.property.2⟩
  loopless e h := G.loopless e.val (congrArg Subtype.val h)

theorem card_filter_subtype (P Q : E → Prop) :
    (Finset.univ.filter (fun e : {e : E // P e} => Q e.val)).card =
      (Finset.univ.filter (fun e : E => P e ∧ Q e)).card := by
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact ⟨e.property, he⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact ⟨⟨e, he.1⟩, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he.2, rfl⟩

theorem degree_induced_graph (C : Finset V) (v : InducedVertex C) :
    degree (inducedGraph G C) v = degreeInto G C v.val := by
  unfold degree degreeInto incidentInto
  simp only [Finset.mem_univ, and_true, inducedGraph, Subtype.ext_iff]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rcases he with hl | hr
    · exact Or.inl ⟨hl, e.property.2⟩
    · exact Or.inr ⟨hr, e.property.1⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with ⟨hl, hrC⟩ | ⟨hr, hlC⟩
    · refine ⟨⟨e, hl ▸ v.property, hrC⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using Or.inl hl
    · refine ⟨⟨e, hlC, hr ▸ v.property⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using Or.inr hr

/-- Exactly the original copies surviving the held contraction. -/
def retained (A B : Finset V) (e : E) : Prop :=
  (G.left e ∈ A ∧ G.right e ∈ A) ∨
    (G.left e ∈ A ∧ G.left e ∈ B ∧ G.right e ∉ A) ∨
    (G.right e ∈ A ∧ G.right e ∈ B ∧ G.left e ∉ A)

abbrev HeldEdge (A B : Finset V) := {e : E // retained G A B e}

/-- The literal contraction of outside vertices; none is its single sink. -/
def projectVertex (A : Finset V) (v : V) : Option (InducedVertex A) :=
  if hv : v ∈ A then some ⟨v, hv⟩ else none

omit [Fintype V] in
theorem project_vertex_eq_some_iff (A : Finset V) (v : V) (a : InducedVertex A) :
    projectVertex A v = some a ↔ v = a.val := by
  by_cases hv : v ∈ A
  · simp only [projectVertex, dif_pos hv, Option.some.injEq, Subtype.ext_iff]
  · have hn : v ≠ a.val := fun he => hv (he ▸ a.property)
    simp [projectVertex, hv, hn]

def heldGraph (s : V) (A B : Finset V) (_hs : s ∉ A) (_hBA : B ⊆ A) :
    Multigraph (Option (InducedVertex A)) (HeldEdge G A B) where
  left e := projectVertex A (G.left e.val)
  right e := projectVertex A (G.right e.val)
  loopless e h := by
    rcases e.property with ⟨hl, hr⟩ | ⟨hl, _, hr⟩ | ⟨hr, _, hl⟩
    · simp only [projectVertex, dif_pos hl, dif_pos hr] at h
      exact G.loopless e.val (congrArg Subtype.val (Option.some.inj h))
    · simp only [projectVertex, dif_pos hl, dif_neg hr, Option.some_ne_none] at h
    · simp [projectVertex, hl, hr] at h

omit [Fintype V] in
theorem held_graph_sink (s : V) (A : Finset V) (hs : s ∉ A) :
    projectVertex A s = none := by simp only [projectVertex, dif_neg hs]

theorem retained_incident_iff (A B : Finset V) (_hBA : B ⊆ A)
    (v : InducedVertex A) (e : E) :
    (retained G A B e ∧ (G.left e = v.val ∨ G.right e = v.val)) ↔
      if v.val ∈ B then G.left e = v.val ∨ G.right e = v.val
      else (G.left e = v.val ∧ G.right e ∈ A) ∨
        (G.right e = v.val ∧ G.left e ∈ A) := by
  by_cases hvB : v.val ∈ B
  · simp only [if_pos hvB]
    constructor
    · exact And.right
    · intro h
      rcases h with hl | hr
      · by_cases hrA : G.right e ∈ A
        · exact ⟨Or.inl ⟨hl ▸ v.property, hrA⟩, Or.inl hl⟩
        · exact ⟨Or.inr (Or.inl ⟨hl ▸ v.property, hl ▸ hvB, hrA⟩), Or.inl hl⟩
      · by_cases hlA : G.left e ∈ A
        · exact ⟨Or.inl ⟨hlA, hr ▸ v.property⟩, Or.inr hr⟩
        · exact ⟨Or.inr (Or.inr ⟨hr ▸ v.property, hr ▸ hvB, hlA⟩), Or.inr hr⟩
  · simp only [if_neg hvB]
    constructor
    · rintro ⟨hret, hl | hr⟩
      · rcases hret with ⟨_, hrA⟩ | ⟨_, hlB, _⟩ | ⟨_, _, hlA⟩
        · exact Or.inl ⟨hl, hrA⟩
        · exact (hvB (hl ▸ hlB)).elim
        · exact (hlA (hl ▸ v.property)).elim
      · rcases hret with ⟨hlA, _⟩ | ⟨_, _, hrA⟩ | ⟨_, hrB, _⟩
        · exact Or.inr ⟨hr, hlA⟩
        · exact (hrA (hr ▸ v.property)).elim
        · exact (hvB (hr ▸ hrB)).elim
    · rintro (⟨hl, hrA⟩ | ⟨hr, hlA⟩)
      · exact ⟨Or.inl ⟨hl ▸ v.property, hrA⟩, Or.inl hl⟩
      · exact ⟨Or.inl ⟨hlA, hr ▸ v.property⟩, Or.inr hr⟩

theorem degree_held_graph (s : V) (A B : Finset V) (hs : s ∉ A)
    (hBA : B ⊆ A) (v : InducedVertex A) :
    degree (heldGraph G s A B hs hBA) (some v) =
      if v.val ∈ B then degree G v.val else degreeInto G A v.val := by
  unfold degree degreeInto incidentInto
  simp only [Finset.mem_univ, and_true, heldGraph, project_vertex_eq_some_iff]
  by_cases hvB : v.val ∈ B
  all_goals simp only [hvB, if_true, if_false]
  all_goals apply Finset.card_bij (fun e _ => e.val)
  all_goals try (intro a _ b _ h; exact Subtype.ext h)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact he
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    have hr := (retained_incident_iff G A B hBA v e).mpr (by simpa only [if_pos hvB] using he)
    exact ⟨⟨e, hr.1⟩, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hr.2, rfl⟩
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    simpa only [if_neg hvB] using (retained_incident_iff G A B hBA v e.val).mp ⟨e.property, he⟩
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    have hr := (retained_incident_iff G A B hBA v e).mpr (by simpa only [if_neg hvB] using he)
    exact ⟨⟨e, hr.1⟩, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hr.2, rfl⟩

end
end FiniteAvalanches.Sandpile.Burning
