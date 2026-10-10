module

public import FiniteAvalanches.Sandpile.Burning.TreeInverse

@[expose] public section

/-! Restrict an actual original-copy subset to a literal induced graph. Paths and
forests transport through the original copy projection; no tree certificate is
supplied for the resulting graph. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open FiniteAvalanches.Trees.RootedPaths
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E)

/-- Every retained induced copy keeps exactly its original membership. -/
def restrictCopies (D : Finset V) (t : Finset E) : Finset (InducedEdge G D) :=
  Finset.univ.filter fun e => e.val ∈ t

theorem mem_restrict_copies (D : Finset V) (t : Finset E) (e : InducedEdge G D) :
    e ∈ restrictCopies G D t ↔ e.val ∈ t := by simp [restrictCopies]

theorem induced_reaches_original (D : Finset V) (f : Finset (InducedEdge G D))
    (x y : InducedVertex D)
    (hr : (copiedTreeGraph (inducedGraph G D)).reaches f x y) :
    (copiedTreeGraph G).reaches (f.image Subtype.val) x.val y.val := by
  induction hr with
  | refl => exact .refl
  | @tail y z hr ha ih =>
    obtain ⟨e, he, ha | ha⟩ := ha
    · exact ih.tail ⟨e.val, Finset.mem_image_of_mem Subtype.val he,
        Or.inl ⟨congrArg Subtype.val ha.1, congrArg Subtype.val ha.2⟩⟩
    · exact ih.tail ⟨e.val, Finset.mem_image_of_mem Subtype.val he,
        Or.inr ⟨congrArg Subtype.val ha.1, congrArg Subtype.val ha.2⟩⟩

theorem induced_restrict_forest (D : Finset V) (t : Finset E)
    (ht : (copiedTreeGraph G).is_forest t) :
    (copiedTreeGraph (inducedGraph G D)).is_forest (restrictCopies G D t) := by
  intro e he hr
  apply ht e.val ((mem_restrict_copies G D t e).mp he)
  have hh := induced_reaches_original G D _ _ _ hr
  apply (copiedTreeGraph G).reaches_mono ?_ hh
  intro a ha
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ha
  refine Finset.mem_erase.mpr ⟨?_, (mem_restrict_copies G D t f).mp (Finset.mem_erase.mp hf).2⟩
  intro hfe
  exact (Finset.mem_erase.mp hf).1 (Subtype.ext hfe)

theorem induced_restrict_reaches_of_walk (D : Finset V) (t : Finset E)
    (x y : InducedVertex D) (p : ((copiedTreeGraph G).toSimple t).Walk x.val y.val)
    (hp : ∀ z ∈ p.support, z ∈ D) :
    (copiedTreeGraph (inducedGraph G D)).reaches (restrictCopies G D t) x y := by
  have hm : (((copiedTreeGraph G).toSimple t).induce (D : Set V)) ≤
      (copiedTreeGraph (inducedGraph G D)).toSimple (restrictCopies G D t) := by
    intro a b hab
    obtain ⟨e, he, h | h⟩ := hab
    · change G.left e = a.val ∧ G.right e = b.val at h
      refine ⟨⟨e, by rw [h.1]; exact a.property, by rw [h.2]; exact b.property⟩, ?_, Or.inl ?_⟩
      · exact (mem_restrict_copies G D t _).mpr he
      · exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
    · change G.right e = a.val ∧ G.left e = b.val at h
      refine ⟨⟨e, by rw [h.2]; exact b.property, by rw [h.1]; exact a.property⟩, ?_, Or.inr ?_⟩
      · exact (mem_restrict_copies G D t _).mpr he
      · exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
  exact ((copiedTreeGraph (inducedGraph G D)).toSimple_reachable _ _ _).mp
    ⟨(p.induce (D : Set V) hp).mapLe hm⟩

theorem induced_restrict_is_tree (s : V) (D : Finset V) (hs : s ∈ D)
    (t : (copiedTreeGraph G).SpanningTree)
    (hp : ∀ x ∈ D, ∀ z ∈ (path ((copiedTreeGraph G).toSimple_isTree t.property) s x).support,
      z ∈ D) :
    (copiedTreeGraph (inducedGraph G D)).is_tree Set.univ (restrictCopies G D t.val) := by
  have hr (x : InducedVertex D) :
      (copiedTreeGraph (inducedGraph G D)).reaches (restrictCopies G D t.val) ⟨s, hs⟩ x :=
    induced_restrict_reaches_of_walk G D t.val ⟨s, hs⟩ x
      (path ((copiedTreeGraph G).toSimple_isTree t.property) s x.val) (hp x.val x.property)
  exact ⟨⟨⟨s, hs⟩, Set.mem_univ _⟩, (by intro e he; simp),
    (by intro x hx y hy; exact ((copiedTreeGraph (inducedGraph G D)).reaches_symm (hr x)).trans (hr y)),
    induced_restrict_forest G D t.val t.property.2.2.2⟩

end
end FiniteAvalanches.Sandpile.Burning
