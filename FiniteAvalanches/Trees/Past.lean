module

public import FiniteAvalanches.Trees.Ancestors

@[expose] public section

/-! Every rooted descendant set is the actual component cut off by its outgoing edge copy. -/
open scoped Classical
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : Multigraph V E)

/-- The literal connected component of a after deleting an individual edge copy. -/
def componentAfter (t : Finset E) (e : E) (a : V) : Set V :=
  {x | G.reaches (t.erase e) a x}

theorem cut_components_componentAfter (t : G.SpanningTree) (e : E) (he : e ∈ t.val)
    (a b : V) (hab : (G.left e = a ∧ G.right e = b) ∨
      (G.right e = a ∧ G.left e = b)) :
    G.cut_components (G.componentAfter t.val e a) t.val e := by
  let C := G.componentAfter t.val e a
  have hsep : ¬G.reaches (t.val.erase e) a b := by
    intro h
    apply t.property.2.2.2 e he
    rcases hab with hab | hab
    · simpa [hab.1, hab.2] using h
    · exact G.reaches_symm (by simpa [hab.1, hab.2] using h)
  have ha : a ∈ C := Relation.ReflTransGen.refl
  have hb : b ∉ C := hsep
  have hclass (x : V) : G.reaches (t.val.erase e) a x ∨ G.reaches (t.val.erase e) b x := by
    have h := t.property.2.2.1 a (Set.mem_univ _) x (Set.mem_univ _)
    induction h with
    | refl => exact Or.inl .refl
    | @tail x y _ h ih =>
      obtain ⟨f, hf, hxy⟩ := h
      by_cases hfe : f = e
      · subst f
        rcases hxy with hxy | hxy <;> rcases hab with hab | hab
        · right; rw [← hxy.2, hab.2]; exact .refl
        · left; rw [← hxy.2, hab.1]; exact .refl
        · left; rw [← hxy.2, hab.1]; exact .refl
        · right; rw [← hxy.2, hab.2]; exact .refl
      · have hstep : G.adjacent (t.val.erase e) x y :=
          ⟨f, Finset.mem_erase.mpr ⟨hfe, hf⟩, hxy⟩
        exact ih.imp (fun h => h.tail hstep) (fun h => h.tail hstep)
  have hd (x : V) (hx : x ∉ C) : G.reaches (t.val.erase e) b x :=
    (hclass x).resolve_left hx
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · change G.crosses C e
    rcases hab with hab | hab
    · exact Or.inl ⟨by rw [hab.1]; exact ha, by rw [hab.2]; exact hb⟩
    · exact Or.inr ⟨by rw [hab.2]; exact hb, by rw [hab.1]; exact ha⟩
  · intro f hf
    constructor
    · intro h
      exact h.tail ⟨f, hf, Or.inl ⟨rfl, rfl⟩⟩
    · intro h
      exact h.tail ⟨f, hf, Or.inr ⟨rfl, rfl⟩⟩
  · intro x hx y hy
    exact (G.reaches_symm hx).trans hy
  · intro x hx y hy
    exact (G.reaches_symm (hd x hx)).trans (hd y hy)

/-- A parent edge is an original tree copy from a to the next vertex on its root path. -/
def is_parent_edge (t : G.SpanningTree) (r a : V) (e : E) : Prop :=
  e ∈ t.val ∧
    ((G.left e = a ∧ G.right e = (path (G.toSimple_isTree t.property) a r).snd) ∨
      (G.right e = a ∧ G.left e = (path (G.toSimple_isTree t.property) a r).snd))

theorem existsUnique_parent_edge (t : G.SpanningTree) (r a : V) (hne : a ≠ r) :
    ∃! e, G.is_parent_edge t r a e := by
  let hT := G.toSimple_isTree t.property
  have hp : ¬(path hT a r).Nil := SimpleGraph.Walk.not_nil_of_ne hne
  obtain ⟨e, he, hadj⟩ := (path hT a r).adj_snd hp
  have hep : G.is_parent_edge t r a e := ⟨he, hadj⟩
  refine ⟨e, hep, ?_⟩
  intro f hf
  apply G.edge_injOn_of_is_forest t.property.2.2.2 hf.1 he
  have hedge {g : E} (hg : G.is_parent_edge t r a g) :
      G.edge g = s(a, (path hT a r).snd) := by
    rcases hg.2 with hg | hg
    · simp only [edge, hg.1, hg.2]
    · simp only [edge, hg.1, hg.2, Sym2.eq_swap]
  exact (hedge hf).trans (hedge hep).symm

/-- The unique outgoing original edge copy; chosen only after full uniqueness. -/
noncomputable def parentEdge (t : G.SpanningTree) (r a : V) (hne : a ≠ r) : E :=
  (G.existsUnique_parent_edge t r a hne).choose

theorem parentEdge_spec (t : G.SpanningTree) (r a : V) (hne : a ≠ r) :
    G.is_parent_edge t r a (G.parentEdge t r a hne) :=
  (G.existsUnique_parent_edge t r a hne).choose_spec.1

/-- The source past on its exact nonroot carrier: the component after the outgoing copy. -/
noncomputable def past (t : G.SpanningTree) (r a : V) (hne : a ≠ r) : Set V :=
  G.componentAfter t.val (G.parentEdge t r a hne) a

theorem past_eq_descendants (t : G.SpanningTree) (r a : V) (hne : a ≠ r) :
    G.past t r a hne = G.descendants t r a := by
  let hT := G.toSimple_isTree t.property
  let e := G.parentEdge t r a hne
  have he := G.parentEdge_spec t r a hne
  let C := G.componentAfter t.val e a
  have hcut := G.cut_components_componentAfter t e he.1 a (path hT a r).snd he.2
  have hr : r ∉ C := by
    obtain ⟨b, hab, q, hp⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne (path hT a r)
    have hq : q.IsPath ∧ a ∉ q.support := by
      have h := path_isPath hT a r
      rw [hp, SimpleGraph.Walk.cons_isPath_iff] at h
      exact h
    have hsnd : (path hT a r).snd = b := by simp [hp]
    have heab : (G.left e = a ∧ G.right e = b) ∨ (G.right e = a ∧ G.left e = b) := by
      simpa [hsnd] using he.2
    have hreach := G.walk_reaches_erase_of_not_mem
      (heab.imp (fun h => h.1) (fun h => h.1)) q hq.2
    intro h
    have hab' : G.reaches (t.val.erase e) a b := h.trans (G.reaches_symm hreach)
    apply t.property.2.2.2 e he.1
    rcases heab with h | h
    · simpa [h.1, h.2] using hab'
    · exact G.reaches_symm (by simpa [h.1, h.2] using hab')
  exact (G.descendants_eq_cut ⟨(t.val, e), t.property, hcut⟩ r a hr
    Relation.ReflTransGen.refl (he.2.imp (fun h => h.1) (fun h => h.1))).symm

/-- Every nonroot vertex has exactly its paper-defined outgoing-edge past. -/
theorem past_ancestor_eq_cut_iff {C S : Set V} (p : G.CutTree C) (r v : V)
    (hr : r ∉ C) (hv : v ∈ C) (hSC : S ⊆ C) (hS : S.Nonempty)
    (hve : G.left p.val.2 = v ∨ G.right p.val.2 = v) :
    ∃ hne : G.ancestorOf ⟨p.val.1, p.property.1⟩ r S hS ≠ r,
      (G.past ⟨p.val.1, p.property.1⟩ r
        (G.ancestorOf ⟨p.val.1, p.property.1⟩ r S hS) hne = C ↔
          v ∈ G.span ⟨p.val.1, p.property.1⟩ S) := by
  let t : G.SpanningTree := ⟨p.val.1, p.property.1⟩
  have hd := G.descendants_eq_cut p r v hr hv hve
  have hca := commonAncestor_spec (G.toSimple_isTree t.property) r S hS
  have hcav : G.ancestorOf t r S hS ∈ C := by
    rw [← hd]
    exact hca.2 v (fun x hx => by change x ∈ G.descendants t r v; rw [hd]; exact hSC hx)
  have hne : G.ancestorOf t r S hS ≠ r := fun h => hr (h ▸ hcav)
  refine ⟨hne, ?_⟩
  rw [G.past_eq_descendants]
  exact G.ancestor_descendants_eq_cut_iff p r v hr hv hSC hS hve

end FiniteAvalanches.Trees.Multigraph
