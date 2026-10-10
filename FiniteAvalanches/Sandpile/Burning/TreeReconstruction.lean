module

public import FiniteAvalanches.Sandpile.Burning.HeldTreeRestriction

@[expose] public section

/-! Reconstruct actual original-copy past geometry from the two literal trees.
The complement tree supplies the root paths outside the shape; every crossing
copy enters at a held vertex. These prove the prescribed union of actual pasts. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open FiniteAvalanches.Trees.RootedPaths
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V) (A B : Finset V) (hs : s ∉ A) (hBA : B ⊆ A)
    (d : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree)
    (a : (copiedTreeGraph (heldGraph G s A B hs hBA)).SpanningTree)

theorem restrict_lift_complement :
    restrictCopies G (Finset.univ \ A) (liftTreeCopies G s A B hs hBA d a) = d.val := by
  ext e
  rw [mem_restrict_copies]
  constructor
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
      exact Subtype.val_injective hfe ▸ hf
    · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
      have hret := f.property
      rw [hfe] at hret
      rcases hret with h | h | h
      · exact False.elim ((Finset.mem_sdiff.mp e.property.1).2 h.1)
      · exact False.elim ((Finset.mem_sdiff.mp e.property.1).2 h.1)
      · exact False.elim ((Finset.mem_sdiff.mp e.property.2).2 h.1)
  · intro he
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem Subtype.val he)

theorem restrict_lift_held :
    restrictHeldCopies G A B (liftTreeCopies G s A B hs hBA d a) = a.val := by
  ext e
  rw [mem_restrict_held_copies]
  constructor
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
      have hret := e.property
      rw [← hfe] at hret
      rcases hret with h | h | h
      · exact False.elim ((Finset.mem_sdiff.mp f.property.1).2 h.1)
      · exact False.elim ((Finset.mem_sdiff.mp f.property.1).2 h.1)
      · exact False.elim ((Finset.mem_sdiff.mp f.property.2).2 h.1)
    · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
      exact Subtype.val_injective hfe ▸ hf
  · intro he
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem Subtype.val he)

theorem lifted_root_path_in_complement (x : V) (hx : x ∉ A) :
    ∀ z ∈ (path ((copiedTreeGraph G).toSimple_isTree
      (liftHeldTrees G s A B hs hBA d a).property) s x).support, z ∉ A := by
  let sD : InducedVertex (Finset.univ \ A) := ⟨s, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hs⟩⟩
  let xD : InducedVertex (Finset.univ \ A) := ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩
  let f : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).toSimple d.val →g
      (copiedTreeGraph G).toSimple (liftHeldTrees G s A B hs hBA d a).val :=
    { toFun := Subtype.val
      map_rel' := by
        intro u v huv
        obtain ⟨e, he, h | h⟩ := huv
        · exact ⟨e.val, Finset.mem_union_left _ (Finset.mem_image_of_mem Subtype.val he),
            Or.inl ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩⟩
        · exact ⟨e.val, Finset.mem_union_left _ (Finset.mem_image_of_mem Subtype.val he),
            Or.inr ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩⟩ }
  let p := path ((copiedTreeGraph (inducedGraph G (Finset.univ \ A))).toSimple_isTree d.property) sD xD
  have hp : (p.map f).IsPath := (SimpleGraph.Walk.isPath_map_iff_of_injective
    (p := p) (f := f) Subtype.val_injective).mpr (path_isPath _ _ _)
  have he := path_eq ((copiedTreeGraph G).toSimple_isTree
    (liftHeldTrees G s A B hs hBA d a).property) (p.map f) hp
  change path ((copiedTreeGraph G).toSimple_isTree
    (liftHeldTrees G s A B hs hBA d a).property) s x = p.map f at he
  intro z hz
  rw [he, SimpleGraph.Walk.support_map] at hz
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
  exact (Finset.mem_sdiff.mp v.property).2

theorem lifted_crossing_held (x y : V)
    (hxy : (copiedTreeGraph G).adjacent (liftHeldTrees G s A B hs hBA d a).val x y)
    (hx : x ∈ A) (hy : y ∉ A) : x ∈ B := by
  obtain ⟨e, he, h | h⟩ := hxy
  · change G.left e = x ∧ G.right e = y at h
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      exact False.elim ((Finset.mem_sdiff.mp f.property.1).2 (h.1.symm ▸ hx))
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      rcases f.property with hr | hr | hr
      · exact False.elim (hy (h.2 ▸ hr.2))
      · exact h.1 ▸ hr.2.1
      · exact False.elim (hr.2.2 (h.1.symm ▸ hx))
  · change G.right e = x ∧ G.left e = y at h
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      exact False.elim ((Finset.mem_sdiff.mp f.property.2).2 (h.1.symm ▸ hx))
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      rcases f.property with hr | hr | hr
      · exact False.elim (hy (h.2 ▸ hr.1))
      · exact False.elim (hr.2.2 (h.1.symm ▸ hx))
      · exact h.1 ▸ hr.2.1

/-- Any actual lifted walk from the complement to the shape visits a held vertex. -/
theorem lifted_walk_avoiding_held {x y : V}
    (p : ((copiedTreeGraph G).toSimple (liftHeldTrees G s A B hs hBA d a).val).Walk x y)
    (hx : x ∉ A) (hp : ∀ z ∈ p.support, z ∉ B) : y ∉ A := by
  induction p with
  | nil => exact hx
  | @cons x z y h p ih =>
    have hz : z ∉ A := by
      intro hz
      exact hp z (by simp) (lifted_crossing_held G s A B hs hBA d a z x
        ((copiedTreeGraph G).adjacent_symm h) hz hx)
    exact ih hz (fun w hw => hp w (by
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr hw))

theorem lifted_tree_past_union (K : Finset (SourceVertex s)) (hK : K.image Subtype.val = B) :
    treePastUnion G s (liftHeldTrees G s A B hs hBA d a) K = A := by
  ext x
  constructor
  · intro hx
    by_contra hxa
    obtain ⟨b, hb, hanc⟩ := (mem_tree_past_union G s _ K x).mp hx
    have hbA : b.val ∈ A := hBA (hK ▸ Finset.mem_image_of_mem Subtype.val hb)
    exact lifted_root_path_in_complement G s A B hs hBA d a x hxa b.val hanc hbA
  · intro hx
    by_contra hxp
    let p := path ((copiedTreeGraph G).toSimple_isTree
      (liftHeldTrees G s A B hs hBA d a).property) s x
    have hp : ∀ z ∈ p.support, z ∉ B := by
      intro z hz hb
      rw [← hK] at hb
      obtain ⟨b, hbin, rfl⟩ := Finset.mem_image.mp hb
      exact hxp ((mem_tree_past_union G s _ K x).mpr ⟨b, hbin, hz⟩)
    exact lifted_walk_avoiding_held G s A B hs hBA d a p hs hp hx

end
end FiniteAvalanches.Sandpile.Burning
