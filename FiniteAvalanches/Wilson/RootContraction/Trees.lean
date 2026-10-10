import FiniteAvalanches.Wilson.RootContraction.Forests

/-! Lifting a copied quotient tree gives one prescribed original root per component. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
  (R : CopiedNetwork.Roots (V := V))

theorem root_cover_of_reaches (t : Finset (Copy G R)) {x : V}
    (h : (graph G R).reaches t (project R x) none) :
    ∃ r ∈ R.val, G.reaches (liftCopies G R t) x r := by
  have hall (z : Vertex R) (hz : (graph G R).reaches t none z) :
      ∀ v, project R v = z → ∃ r ∈ R.val, G.reaches (liftCopies G R t) v r := by
    induction hz with
    | refl =>
      intro v hv
      exact ⟨v, (project_eq_none R v).mp hv, .refl⟩
    | @tail a b _ he ih =>
      intro v hv
      by_cases hr : v ∈ R.val
      · exact ⟨v, hr, .refl⟩
      obtain ⟨e, he, h | h⟩ := he
      · have hva : v = G.right e.val :=
          ((project_eq_iff R v _).mp (hv.trans h.2.symm)).resolve_right (fun hh => hr hh.1)
        subst v
        obtain ⟨r, hr, hp⟩ := ih _ h.1
        have hstep : G.reaches (liftCopies G R t) (G.right e.val) (G.left e.val) :=
          .single ⟨e.val, (mem_liftCopies G R t e).mpr he, Or.inr ⟨rfl, rfl⟩⟩
        exact ⟨r, hr, hstep.trans hp⟩
      · have hva : v = G.left e.val :=
          ((project_eq_iff R v _).mp (hv.trans h.2.symm)).resolve_right (fun hh => hr hh.1)
        subst v
        obtain ⟨r, hr, hp⟩ := ih _ h.1
        have hstep : G.reaches (liftCopies G R t) (G.left e.val) (G.right e.val) :=
          .single ⟨e.val, (mem_liftCopies G R t e).mpr he, Or.inl ⟨rfl, rfl⟩⟩
        exact ⟨r, hr, hstep.trans hp⟩
  exact hall _ ((graph G R).reaches_symm h) x rfl

theorem forest_of_quotient_forest {t : Finset (Copy G R)} (ht : (graph G R).is_forest t) :
    G.is_forest (liftCopies G R t) := by
  intro e he halt
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  apply ht f hf
  exact (graph G R).reaches_mono (project_erase_lift_subset G R t f)
    (reaches_project_copies G R halt)

/-- Distinct prescribed roots cannot become connected when lifting a quotient forest. -/
theorem roots_eq_of_reaches {t : Finset (Copy G R)} (ht : (graph G R).is_forest t)
    {r s : V} (hr : r ∈ R.val) (hs : s ∈ R.val)
    (h : G.reaches (liftCopies G R t) r s) : r = s := by
  obtain ⟨p⟩ := (G.toSimple_reachable _ r s).mpr h
  have hp := p.toPath.property
  generalize hq : p.toPath.val = q at hp
  cases q with
  | nil => rfl
  | @cons r z s hadj q =>
    have hnot : r ∉ q.support := (SimpleGraph.Walk.cons_isPath_iff hadj q).mp hp |>.2
    obtain ⟨e, he, h | h⟩ := hadj
    all_goals
      obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
      have heincident : G.left e = r ∨ G.right e = r := by
        first | exact Or.inl h.1 | exact Or.inr h.1
      have htail := G.walk_reaches_erase_of_not_mem heincident q hnot
      have hproject := (graph G R).reaches_mono (project_erase_lift_subset G R t f)
        (by simpa only [hfe] using reaches_project_copies G R htail)
      apply False.elim
      apply ht f hf
      have hrp := (project_eq_none R r).mpr hr
      have hsp := (project_eq_none R s).mpr hs
      first
      | exact (graph G R).reaches_symm (by
          simpa only [graph, hfe, h.1, h.2, hrp, hsp] using hproject)
      | exact (by simpa only [graph, hfe, h.1, h.2, hrp, hsp] using hproject)

theorem rooted_forest_of_tree {t : Finset (Copy G R)} (ht : (graph G R).is_tree Set.univ t) :
    G.is_rooted_forest R.val (liftCopies G R t) := by
  refine ⟨forest_of_quotient_forest G R ht.2.2.2, ?_⟩
  intro x
  obtain ⟨r, hr, hxr⟩ := root_cover_of_reaches G R t
    (ht.2.2.1 _ (Set.mem_univ _) none (Set.mem_univ _))
  refine ⟨r, hr, hxr, ?_⟩
  intro s hs hxs
  exact roots_eq_of_reaches G R ht.2.2.2 hs hr ((G.reaches_symm hxs).trans hxr)

end
end FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
