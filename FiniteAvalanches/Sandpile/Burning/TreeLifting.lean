module

public import FiniteAvalanches.Sandpile.Burning.TreeRestriction

@[expose] public section

/-! Lift literal induced-complement and held-graph tree copies to the original
carrier. Connectivity is proved by lifting contracted walks through the actual
complement tree; the exact copy count then certifies a canonical spanning tree. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V) (A B : Finset V) (hs : s ∉ A) (hBA : B ⊆ A)

def liftTreeCopies
    (d : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree)
    (a : (copiedTreeGraph (heldGraph G s A B hs hBA)).SpanningTree) : Finset E :=
  d.val.image Subtype.val ∪ a.val.image Subtype.val

/-- The contracted sink represents the original sink; active vertices represent themselves. -/
def heldVertexRep (v : Option (InducedVertex A)) : V := match v with
  | none => s
  | some x => x.val

omit [Fintype V] in
include hs in
theorem project_held_vertex_rep (v : Option (InducedVertex A)) :
    projectVertex A (heldVertexRep s A v) = v := by
  cases v with
  | none => exact held_graph_sink s A hs
  | some x => simp [heldVertexRep, projectVertex, x.property]

theorem lift_fiber_connected
    (d : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree)
    (a : (copiedTreeGraph (heldGraph G s A B hs hBA)).SpanningTree)
    (x y : V) (hxy : projectVertex A x = projectVertex A y) :
    (copiedTreeGraph G).reaches (liftTreeCopies G s A B hs hBA d a) x y := by
  by_cases hx : x ∈ A
  · have hy : y ∈ A := by
      by_contra hy
      simp only [projectVertex, dif_pos hx, dif_neg hy, Option.some_ne_none] at hxy
    have he : x = y := by
      simpa only [projectVertex, dif_pos hx, dif_pos hy, Option.some.injEq, Subtype.ext_iff] using hxy
    subst y
    exact .refl
  · have hy : y ∉ A := by
      intro hy
      simp [projectVertex, hx, hy] at hxy
    let xD : InducedVertex (Finset.univ \ A) := ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩
    let yD : InducedVertex (Finset.univ \ A) := ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩⟩
    exact (copiedTreeGraph G).reaches_mono Finset.subset_union_left
      (induced_reaches_original G _ d.val xD yD
        (d.property.2.2.1 xD (Set.mem_univ _) yD (Set.mem_univ _)))

theorem held_adjacent_lift
    (d : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree)
    (a : (copiedTreeGraph (heldGraph G s A B hs hBA)).SpanningTree)
    (p q : Option (InducedVertex A))
    (hpq : (copiedTreeGraph (heldGraph G s A B hs hBA)).adjacent a.val p q)
    (x y : V) (hx : projectVertex A x = p) (hy : projectVertex A y = q) :
    (copiedTreeGraph G).reaches (liftTreeCopies G s A B hs hBA d a) x y := by
  obtain ⟨e, he, h | h⟩ := hpq
  · have h1 := lift_fiber_connected G s A B hs hBA d a x (G.left e.val) (hx.trans h.1.symm)
    have h2 := lift_fiber_connected G s A B hs hBA d a (G.right e.val) y (h.2.trans hy.symm)
    exact h1.trans ((Relation.ReflTransGen.single
      ⟨e.val, Finset.mem_union_right _ (Finset.mem_image_of_mem Subtype.val he),
        Or.inl ⟨rfl,rfl⟩⟩).trans h2)
  · have h1 := lift_fiber_connected G s A B hs hBA d a x (G.right e.val) (hx.trans h.1.symm)
    have h2 := lift_fiber_connected G s A B hs hBA d a (G.left e.val) y (h.2.trans hy.symm)
    exact h1.trans ((Relation.ReflTransGen.single
      ⟨e.val, Finset.mem_union_right _ (Finset.mem_image_of_mem Subtype.val he),
        Or.inr ⟨rfl,rfl⟩⟩).trans h2)

theorem held_reaches_lift
    (d : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree)
    (a : (copiedTreeGraph (heldGraph G s A B hs hBA)).SpanningTree)
    (p q : Option (InducedVertex A))
    (hpq : (copiedTreeGraph (heldGraph G s A B hs hBA)).reaches a.val p q) :
    ∀ x, projectVertex A x = p → ∀ y, projectVertex A y = q →
      (copiedTreeGraph G).reaches (liftTreeCopies G s A B hs hBA d a) x y := by
  induction hpq with
  | refl => intro x hx y hy; exact lift_fiber_connected G s A B hs hBA d a x y (hx.trans hy.symm)
  | @tail m n hr ha ih =>
    intro x hx y hy
    exact (ih x hx (heldVertexRep s A m) (project_held_vertex_rep s A hs m)).trans
      (held_adjacent_lift G s A B hs hBA d a m n ha (heldVertexRep s A m) y
        (project_held_vertex_rep s A hs m) hy)

theorem lifted_tree_connected
    (d : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree)
    (a : (copiedTreeGraph (heldGraph G s A B hs hBA)).SpanningTree) (x y : V) :
    (copiedTreeGraph G).reaches (liftTreeCopies G s A B hs hBA d a) x y :=
  held_reaches_lift G s A B hs hBA d a _ _
    (a.property.2.2.1 _ (Set.mem_univ _) _ (Set.mem_univ _)) x rfl y rfl

theorem lift_tree_copies_disjoint
    (d : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree)
    (a : (copiedTreeGraph (heldGraph G s A B hs hBA)).SpanningTree) :
    Disjoint (d.val.image Subtype.val) (a.val.image Subtype.val) := by
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

theorem lift_tree_copies_card
    (d : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree)
    (a : (copiedTreeGraph (heldGraph G s A B hs hBA)).SpanningTree) :
    (liftTreeCopies G s A B hs hBA d a).card + 1 = Fintype.card V := by
  unfold liftTreeCopies
  rw [Finset.card_union_of_disjoint (lift_tree_copies_disjoint G s A B hs hBA d a),
    Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_image_of_injective _ Subtype.val_injective]
  have hd := copied_tree_card (copiedTreeGraph (inducedGraph G (Finset.univ \ A))) d
  have ha := copied_tree_card (copiedTreeGraph (heldGraph G s A B hs hBA)) a
  rw [Fintype.card_option, Fintype.card_coe] at ha
  rw [Fintype.card_coe] at hd
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  rw [Finset.card_univ] at hsum
  omega

/-- The actual lifted original copies, with their fully proved tree certificate. -/
def liftHeldTrees
    (d : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree)
    (a : (copiedTreeGraph (heldGraph G s A B hs hBA)).SpanningTree) :
    (copiedTreeGraph G).SpanningTree :=
  ⟨liftTreeCopies G s A B hs hBA d a, copied_tree_of_connected_card (copiedTreeGraph G) s _
    (lifted_tree_connected G s A B hs hBA d a) (lift_tree_copies_card G s A B hs hBA d a)⟩

end
end FiniteAvalanches.Sandpile.Burning
