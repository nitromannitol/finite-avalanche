module

public import FiniteAvalanches.Trees.Joining

@[expose] public section

/-! Degrees count individual original copies. Looplessness makes the two
incidence orientations exclusive; no endpoint quotient or simple graph is used. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E)

def incidentInto (A : Finset V) (v : V) : Finset E :=
  Finset.univ.filter fun e =>
    (G.left e = v ∧ G.right e ∈ A) ∨ (G.right e = v ∧ G.left e ∈ A)

def degreeInto (A : Finset V) (v : V) : ℕ := (incidentInto G A v).card

def degree (v : V) : ℕ := degreeInto G Finset.univ v

theorem degree_into_mono {A B : Finset V} (h : A ⊆ B) (v : V) :
    degreeInto G A v ≤ degreeInto G B v := by
  apply Finset.card_le_card
  intro e he
  simp only [incidentInto, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · exact Or.inl ⟨hl, h hr⟩
  · exact Or.inr ⟨hr, h hl⟩

theorem degree_into_le_degree (A : Finset V) (v : V) : degreeInto G A v ≤ degree G v :=
  degree_into_mono G (Finset.subset_univ A) v

theorem incident_into_union (A B : Finset V) (v : V) :
    incidentInto G (A ∪ B) v = incidentInto G A v ∪ incidentInto G B v := by
  ext e
  simp only [incidentInto, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  tauto

theorem incident_into_disjoint {A B : Finset V} (h : Disjoint A B) (v : V) :
    Disjoint (incidentInto G A v) (incidentInto G B v) := by
  apply Finset.disjoint_left.mpr
  intro e ha hb
  simp only [incidentInto, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rcases ha with ⟨hl, hra⟩ | ⟨hr, hla⟩
  · rcases hb with ⟨_, hrb⟩ | ⟨hr, _⟩
    · exact Finset.disjoint_left.mp h hra hrb
    · exact G.loopless e (hl.trans hr.symm)
  · rcases hb with ⟨hl, _⟩ | ⟨_, hlb⟩
    · exact G.loopless e (hl.trans hr.symm)
    · exact Finset.disjoint_left.mp h hla hlb

theorem degree_into_union {A B : Finset V} (h : Disjoint A B) (v : V) :
    degreeInto G (A ∪ B) v = degreeInto G A v + degreeInto G B v := by
  unfold degreeInto
  rw [incident_into_union, Finset.card_union_of_disjoint (incident_into_disjoint G h v)]

theorem degree_into_compl (A : Finset V) (v : V) :
    degreeInto G (Finset.univ \ A) v + degreeInto G A v = degree G v := by
  rw [← degree_into_union G Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union,
    Finset.union_eq_left.mpr (Finset.subset_univ A)]
  rfl

theorem degree_into_le_sdiff_add (H A : Finset V) (v : V) :
    degreeInto G H v ≤ degreeInto G (H \ A) v + degreeInto G A v := by
  have hsub : H ⊆ (H \ A) ∪ A := by intro x hx; by_cases ha : x ∈ A <;> simp_all
  exact (degree_into_mono G hsub v).trans (by
    rw [degree_into_union G Finset.sdiff_disjoint])

theorem degree_into_self (v : V) : degreeInto G {v} v = 0 := by
  have he : incidentInto G {v} v = ∅ := by
    ext e
    simp only [incidentInto, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro (⟨hl, hr⟩ | ⟨hr, hl⟩)
    all_goals exact G.loopless e (hl.trans hr.symm)
  simp [degreeInto, he]

end
end FiniteAvalanches.Sandpile.Burning
