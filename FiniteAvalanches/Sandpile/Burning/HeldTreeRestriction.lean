module

public import FiniteAvalanches.Sandpile.Burning.TreeLifting
public import FiniteAvalanches.Sandpile.Burning.PastGeometry

@[expose] public section

/-! The actual past union leaves a root-connected induced complement. Every other
selected copy survives the literal held contraction. Their partition and exact
counts certify both restricted trees, without a supplied tree or stopping law. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open FiniteAvalanches.Trees.RootedPaths
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E)

def restrictHeldCopies (A B : Finset V) (t : Finset E) : Finset (HeldEdge G A B) :=
  Finset.univ.filter fun e => e.val ∈ t

omit [DecidableEq V] in
theorem mem_restrict_held_copies (A B : Finset V) (t : Finset E) (e : HeldEdge G A B) :
    e ∈ restrictHeldCopies G A B t ↔ e.val ∈ t := by simp [restrictHeldCopies]

theorem original_copies_partition (A B : Finset V) (t : Finset E)
    (hc : ∀ e ∈ t, (G.left e ∉ A ∧ G.right e ∉ A) ∨ retained G A B e) :
    (restrictCopies G (Finset.univ \ A) t).image Subtype.val ∪
      (restrictHeldCopies G A B t).image Subtype.val = t := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      exact (mem_restrict_copies G _ t f).mp hf
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      exact (mem_restrict_held_copies G A B t f).mp hf
  · intro he
    rcases hc e he with hd | ha
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hd.1⟩,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hd.2⟩⟩,
          (mem_restrict_copies G _ t _).mpr he, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨⟨e, ha⟩, (mem_restrict_held_copies G A B t _).mpr he, rfl⟩)

theorem restricted_copies_disjoint (A B : Finset V) (t : Finset E) :
    Disjoint ((restrictCopies G (Finset.univ \ A) t).image Subtype.val)
      ((restrictHeldCopies G A B t).image Subtype.val) := by
  apply Finset.disjoint_left.mpr
  intro e hd ha
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨g, hg, hge⟩ := Finset.mem_image.mp ha
  have hl := (Finset.mem_sdiff.mp f.property.1).2
  have hr := (Finset.mem_sdiff.mp f.property.2).2
  have hret := g.property
  rw [hge] at hret
  rcases hret with h | h | h
  · exact hl h.1
  · exact hl h.1
  · exact hr h.1

variable (s : V) (A B : Finset V) (hs : s ∉ A) (hBA : B ⊆ A)

theorem original_reaches_project (t : Finset E)
    (hc : ∀ e ∈ t, (G.left e ∉ A ∧ G.right e ∉ A) ∨ retained G A B e)
    (x y : V) (hr : (copiedTreeGraph G).reaches t x y) :
    (copiedTreeGraph (heldGraph G s A B hs hBA)).reaches (restrictHeldCopies G A B t)
      (projectVertex A x) (projectVertex A y) := by
  induction hr with
  | refl => exact .refl
  | @tail y z hr ha ih =>
    obtain ⟨e, he, h | h⟩ := ha
    · change G.left e = y ∧ G.right e = z at h
      rcases hc e he with hd | hret
      · have hy : y ∉ A := h.1 ▸ hd.1
        have hz : z ∉ A := h.2 ▸ hd.2
        simpa only [projectVertex, dif_neg hy, dif_neg hz] using ih
      · exact ih.tail ⟨⟨e, hret⟩, (mem_restrict_held_copies G A B t _).mpr he,
          Or.inl ⟨congrArg (projectVertex A) h.1, congrArg (projectVertex A) h.2⟩⟩
    · change G.right e = y ∧ G.left e = z at h
      rcases hc e he with hd | hret
      · have hy : y ∉ A := h.1 ▸ hd.2
        have hz : z ∉ A := h.2 ▸ hd.1
        simpa only [projectVertex, dif_neg hy, dif_neg hz] using ih
      · exact ih.tail ⟨⟨e, hret⟩, (mem_restrict_held_copies G A B t _).mpr he,
          Or.inr ⟨congrArg (projectVertex A) h.1, congrArg (projectVertex A) h.2⟩⟩

theorem held_restriction_connected (t : (copiedTreeGraph G).SpanningTree)
    (hc : ∀ e ∈ t.val, (G.left e ∉ A ∧ G.right e ∉ A) ∨ retained G A B e)
    (x y : Option (InducedVertex A)) :
    (copiedTreeGraph (heldGraph G s A B hs hBA)).reaches (restrictHeldCopies G A B t.val) x y := by
  have hr := original_reaches_project G s A B hs hBA t.val hc
    (heldVertexRep s A x) (heldVertexRep s A y)
    (t.property.2.2.1 _ (Set.mem_univ _) _ (Set.mem_univ _))
  simpa only [project_held_vertex_rep s A hs] using hr

/-- The root-connected complement's proved size supplies the remaining held-copy count. -/
theorem held_restriction_card (t : (copiedTreeGraph G).SpanningTree)
    (hc : ∀ e ∈ t.val, (G.left e ∉ A ∧ G.right e ∉ A) ∨ retained G A B e)
    (hd : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).is_tree Set.univ
      (restrictCopies G (Finset.univ \ A) t.val)) :
    (restrictHeldCopies G A B t.val).card + 1 = Fintype.card (Option (InducedVertex A)) := by
  have ht := copied_tree_card (copiedTreeGraph G) t
  have hdc := copied_tree_card (copiedTreeGraph (inducedGraph G (Finset.univ \ A))) ⟨_, hd⟩
  have hsum := congrArg Finset.card (original_copies_partition G A B t.val hc)
  rw [Finset.card_union_of_disjoint (restricted_copies_disjoint G A B t.val),
    Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_image_of_injective _ Subtype.val_injective] at hsum
  change (restrictCopies G (Finset.univ \ A) t.val).card + 1 =
    Fintype.card (InducedVertex (Finset.univ \ A)) at hdc
  rw [Fintype.card_coe] at hdc
  rw [Fintype.card_option, Fintype.card_coe]
  have hparts := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  rw [Finset.card_univ] at hparts
  omega

/-- A general restriction certificate; its geometric premises are proved below for actual pasts. -/
theorem held_restriction_is_tree (t : (copiedTreeGraph G).SpanningTree)
    (hc : ∀ e ∈ t.val, (G.left e ∉ A ∧ G.right e ∉ A) ∨ retained G A B e)
    (hd : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).is_tree Set.univ
      (restrictCopies G (Finset.univ \ A) t.val)) :
    (copiedTreeGraph (heldGraph G s A B hs hBA)).is_tree Set.univ (restrictHeldCopies G A B t.val) :=
  copied_tree_of_connected_card (copiedTreeGraph (heldGraph G s A B hs hBA)) none _
    (held_restriction_connected G s A B hs hBA t hc) (held_restriction_card G A B t hc hd)

variable (t : (copiedTreeGraph G).SpanningTree) (K : Finset (SourceVertex s))

theorem past_tree_edge_partition (e : E) (he : e ∈ t.val) :
    (G.left e ∉ treePastUnion G s t K ∧ G.right e ∉ treePastUnion G s t K) ∨
      retained G (treePastUnion G s t K) (K.image Subtype.val) e := by
  by_cases hl : G.left e ∈ treePastUnion G s t K
  · by_cases hr : G.right e ∈ treePastUnion G s t K
    · exact Or.inr (Or.inl ⟨hl, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hl, tree_past_union_crossing_held G s t K _ _
        ⟨e, he, Or.inl ⟨rfl,rfl⟩⟩ hl hr, hr⟩))
  · by_cases hr : G.right e ∈ treePastUnion G s t K
    · exact Or.inr (Or.inr (Or.inr ⟨hr, tree_past_union_crossing_held G s t K _ _
        ⟨e, he, Or.inr ⟨rfl,rfl⟩⟩ hr hl, hl⟩))
    · exact Or.inl ⟨hl,hr⟩

theorem past_complement_tree_certificate :
    (copiedTreeGraph (inducedGraph G (Finset.univ \ treePastUnion G s t K))).is_tree Set.univ
      (restrictCopies G (Finset.univ \ treePastUnion G s t K) t.val) := by
  apply induced_restrict_is_tree G s _
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, tree_past_union_avoids_sink G s t K⟩) t
  intro x hx z hz
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
    root_path_avoids_tree_past_union G s t K x (Finset.mem_sdiff.mp hx).2 z hz⟩

/-- Literal restriction to the actual complement of the past union. -/
def complementPastTree :
    (copiedTreeGraph (inducedGraph G (Finset.univ \ treePastUnion G s t K))).SpanningTree :=
  ⟨restrictCopies G _ t.val, past_complement_tree_certificate G s t K⟩

/-- Literal restriction and contraction, deriving its source exclusion and held inclusion first. -/
def heldPastTree :
    (copiedTreeGraph (heldGraph G s (treePastUnion G s t K) (K.image Subtype.val)
      (tree_past_union_avoids_sink G s t K) (held_subset_tree_past_union G s t K))).SpanningTree :=
  ⟨restrictHeldCopies G _ _ t.val, held_restriction_is_tree G s _ _
    (tree_past_union_avoids_sink G s t K) (held_subset_tree_past_union G s t K) t
    (past_tree_edge_partition G s t K) (past_complement_tree_certificate G s t K)⟩

end
end FiniteAvalanches.Sandpile.Burning
