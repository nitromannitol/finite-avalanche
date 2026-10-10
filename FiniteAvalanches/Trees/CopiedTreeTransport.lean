import FiniteAvalanches.Trees.Joining

/-! Ordinary tree transport retains a bijection of individual copied edges.
The unordered endpoint condition permits the orientation reversal of negative
lattice exits when they become internal copies in a larger wired box. -/
set_option autoImplicit false
namespace FiniteAvalanches.Trees.Multigraph
open scoped Classical
noncomputable section
variable {V W E D : Type} [Fintype V] [Fintype W] [Fintype E] [Fintype D]
    [DecidableEq E] [DecidableEq D]
    (G : Multigraph V E) (H : Multigraph W D) (v : V ≃ W) (e : E ≃ D)
    (hend : ∀ a, (H.left (e a) = v (G.left a) ∧ H.right (e a) = v (G.right a)) ∨
      (H.left (e a) = v (G.right a) ∧ H.right (e a) = v (G.left a)))

include v hend

omit [DecidableEq E] in
theorem copiedEquiv_adjacent_iff (F : Finset E) (x y : V) :
    H.adjacent (F.image e) (v x) (v y) ↔ G.adjacent F x y := by
  constructor
  · rintro ⟨b,hb,hxy⟩
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨a,ha,?_⟩
    rcases hend a with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · simpa only [hl,hr,Equiv.apply_eq_iff_eq] using hxy
    · simpa only [hl,hr,Equiv.apply_eq_iff_eq,or_comm] using hxy
  · rintro ⟨a,ha,hxy⟩
    refine ⟨e a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,?_⟩
    rcases hend a with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · simpa only [hl,hr,Equiv.apply_eq_iff_eq] using hxy
    · simpa only [hl,hr,Equiv.apply_eq_iff_eq,or_comm] using hxy

omit [DecidableEq E] in
theorem copiedEquiv_reaches_iff (F : Finset E) (x y : V) :
    H.reaches (F.image e) (v x) (v y) ↔ G.reaches F x y := by
  constructor
  · intro h
    have h' : G.reaches F (v.symm (v x)) (v.symm (v y)) :=
      Relation.ReflTransGen.lift' v.symm (fun a b hab => by
        apply Relation.ReflTransGen.single
        apply (copiedEquiv_adjacent_iff G H v e hend F (v.symm a) (v.symm b)).mp
        simpa only [Equiv.apply_symm_apply] using hab) _ _ h
    simpa only [Equiv.symm_apply_apply] using h'
  · intro h
    exact Relation.ReflTransGen.lift' v (fun a b hab =>
      Relation.ReflTransGen.single
        ((copiedEquiv_adjacent_iff G H v e hend F a b).mpr hab)) _ _ h

theorem copiedEquiv_forest_iff (F : Finset E) :
    H.is_forest (F.image e) ↔ G.is_forest F := by
  have herase (a : E) : (F.erase a).image e = (F.image e).erase (e a) :=
    Finset.image_erase e.injective F a
  constructor
  · intro h a ha hp
    apply h (e a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    have hp' := (copiedEquiv_reaches_iff G H v e hend (F.erase a) _ _).mpr hp
    rw [herase] at hp'
    rcases hend a with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · simpa only [hl,hr] using hp'
    · simpa only [hl,hr] using H.reaches_symm hp'
  · intro h b hb hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    apply h a ha
    apply (copiedEquiv_reaches_iff G H v e hend (F.erase a) _ _).mp
    rw [herase]
    rcases hend a with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · simpa only [hl,hr] using hp
    · simpa only [hl,hr] using H.reaches_symm hp

/-- Actual spanning trees are transported by the copied-edge bijection; loops
and parallel circuits are tested by the original copied-edge forest predicate. -/
theorem copiedEquiv_tree_iff (F : Finset E) :
    H.is_tree Set.univ (F.image e) ↔ G.is_tree Set.univ F := by
  constructor
  · intro h
    refine ⟨⟨v.symm (Classical.choose h.1),Set.mem_univ _⟩,
      (by intro a ha; exact ⟨Set.mem_univ _,Set.mem_univ _⟩),?_,
      (copiedEquiv_forest_iff G H v e hend F).mp h.2.2.2⟩
    intro x _ y _
    exact (copiedEquiv_reaches_iff G H v e hend F x y).mp
      (h.2.2.1 (v x) (Set.mem_univ _) (v y) (Set.mem_univ _))
  · intro h
    refine ⟨⟨v (Classical.choose h.1),Set.mem_univ _⟩,
      (by intro a ha; exact ⟨Set.mem_univ _,Set.mem_univ _⟩),?_,
      (copiedEquiv_forest_iff G H v e hend F).mpr h.2.2.2⟩
    intro x _ y _
    have hp := (copiedEquiv_reaches_iff G H v e hend F (v.symm x) (v.symm y)).mpr
      (h.2.2.1 (v.symm x) (Set.mem_univ _) (v.symm y) (Set.mem_univ _))
    simpa only [Equiv.apply_symm_apply] using hp

end
end FiniteAvalanches.Trees.Multigraph
