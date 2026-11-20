import FiniteAvalanches.Trees.Lattice.TightEvents

/-! A present edge whose dual edge has its ends joined by present dual edges inside a box
leaves a set of sites inside that box which no other present edge leaves, and a certified
edge at the root side of a wired tree encloses the past behind it. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice

open LatticeProb
open scoped Classical

noncomputable section

/-- Separation by a dual walk inside a centered box. -/
theorem exists_box_separation_of_dual_walk (ω : EdgeField) {a b : Site 2}
    (hab : (toGraph ω).Adj a b) {u v : Site 2}
    (huv : (dualEdgeOf ⟨s(a, b), hab.1⟩).val = s(u, v))
    (P : (toGraph (dualField ω)).Walk v u) (M : ℤ)
    (hP : ∀ z ∈ P.support, |z 0| ≤ M ∧ |z 1| ≤ M) :
    ∃ S : Set (Site 2), (∀ x ∈ S, |x 0| ≤ M ∧ |x 1| ≤ M) ∧ (a ∈ S ↔ b ∉ S) ∧
      ∀ x y, (toGraph ω).Adj x y → s(x, y) ≠ s(a, b) → (x ∈ S ↔ y ∈ S) := by
  obtain ⟨hlat, hω⟩ := hab
  set e : LatticeEdge := ⟨s(a, b), hlat⟩ with he
  have hadj : (lattice 2).Adj u v := by
    have := (dualEdgeOf e).property
    rw [huv] at this
    exact this
  have hdual_false : dualField ω (dualEdgeOf e) = false := by
    rw [dualField_dualEdgeOf, hω]
    rfl
  set Q := P.bypass.mapLe (toGraph_le_lattice (dualField ω)) with hQ
  have hQpath : Q.IsPath := (SimpleGraph.Walk.isPath_mapLe _).mpr P.bypass_isPath
  have hQedges : ∀ d ∈ Q.edges, ∃ hd : d ∈ (lattice 2).edgeSet,
      dualField ω ⟨d, hd⟩ = true := by
    intro d hdQ
    rw [hQ, SimpleGraph.Walk.edges_mapLe_eq_edges] at hdQ
    have hdG := SimpleGraph.Walk.edges_subset_edgeSet _ hdQ
    rw [toGraph_edgeSet] at hdG
    exact hdG
  have hQsupp : ∀ z ∈ Q.support, |z 0| ≤ M ∧ |z 1| ≤ M := by
    intro z hz
    rw [hQ, SimpleGraph.Walk.support_mapLe_eq_support] at hz
    exact hP z (P.support_bypass_subset_support hz)
  have hnot : s(u, v) ∉ Q.edges := by
    intro hmem
    obtain ⟨hd, htrue⟩ := hQedges _ hmem
    have hEq : (⟨s(u, v), hd⟩ : LatticeEdge) = dualEdgeOf e := Subtype.ext huv.symm
    rw [hEq, hdual_false] at htrue
    exact Bool.false_ne_true htrue
  set c : (lattice 2).Walk u u := SimpleGraph.Walk.cons hadj Q with hc
  have hctrail : c.IsTrail :=
    (SimpleGraph.Walk.isTrail_cons hadj Q).mpr ⟨hQpath.isTrail, hnot⟩
  set D : Finset (Sym2 (Site 2)) := hctrail.edgesFinset with hDdef
  have hmemD : ∀ d, d ∈ D ↔ d = s(u, v) ∨ d ∈ Q.edges := by
    intro d
    change d ∈ c.edges ↔ _
    rw [hc, SimpleGraph.Walk.edges_cons, List.mem_cons]
  have hlatD : ∀ d ∈ D, ∃ z : Site 2, ∃ i : Fin 2, d = s(z, z + unit i) := by
    intro d hd
    exact exists_base_of_mem_edgeSet (c.edges_subset_edgeSet hd)
  have hevenD : ∀ w : Site 2, ∑ d ∈ D, (if w ∈ d then 1 else 0 : ZMod 2) = 0 := by
    intro w
    rw [Finset.sum_boole, ZMod.natCast_eq_zero_iff_even]
    have hev := (hctrail.even_countP_edges_iff w).mpr (fun h => absurd rfl h)
    have hcard : (D.filter (fun d => w ∈ d)).card = c.edges.countP (fun d => w ∈ d) := by
      rw [List.countP_eq_length_filter]
      rfl
    simpa [hcard] using hev
  have hboundD : ∀ d ∈ D, ∀ z ∈ d, |z 0| ≤ M ∧ |z 1| ≤ M := by
    intro d hd z hz
    have hzc : z ∈ c.support :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
        (SimpleGraph.Walk.not_nil_cons)).mpr ⟨d, hd, hz⟩
    rw [hc, SimpleGraph.Walk.support_cons, List.mem_cons] at hzc
    rcases hzc with rfl | hzQ
    · exact hQsupp _ Q.end_mem_support
    · exact hQsupp z hzQ
  refine ⟨{x | rayParity D x = 1}, ?_, ?_, ?_⟩
  · intro x hx
    refine rayParity_support_bounded D hlatD hevenD M hboundD x ?_
    simp only [Set.mem_setOf_eq] at hx
    rw [hx]
    decide
  · have h := rayParity_add_of_adj D hlatD hevenD hlat
    have hin : (dualEdgeOf ⟨s(a, b), hlat⟩).val ∈ D := (hmemD _).mpr (Or.inl huv)
    rw [if_pos hin] at h
    simp only [Set.mem_setOf_eq]
    generalize rayParity D a = p at h ⊢
    generalize rayParity D b = p' at h ⊢
    revert p p'
    decide
  · rintro x y ⟨hxy, hωxy⟩ hne
    have h := rayParity_add_of_adj D hlatD hevenD hxy
    have hout : (dualEdgeOf ⟨s(x, y), hxy⟩).val ∉ D := by
      rw [hmemD]
      rintro (h1 | h1)
      · have : dualEdgeOf ⟨s(x, y), hxy⟩ = dualEdgeOf e := Subtype.ext (h1.trans huv.symm)
        exact hne (congrArg Subtype.val (dualEdgeOf_injective this))
      · obtain ⟨hd, htrue⟩ := hQedges _ h1
        have hdf := dualField_dualEdgeOf ω ⟨s(x, y), hxy⟩
        rw [hωxy] at hdf
        have : (⟨(dualEdgeOf ⟨s(x, y), hxy⟩).val, hd⟩ : LatticeEdge) =
            dualEdgeOf ⟨s(x, y), hxy⟩ := rfl
        rw [this, hdf] at htrue
        exact Bool.false_ne_true htrue
    rw [if_neg hout] at h
    simp only [Set.mem_setOf_eq]
    generalize rayParity D x = p at h ⊢
    generalize rayParity D y = p' at h ⊢
    revert p p'
    decide

/-- A dual link inside a set gives a dual walk through it. -/
theorem exists_walk_of_dualLinked {ω : EdgeField} {W : Set (Site 2)} {u v : Site 2}
    (h : DualLinked ω W u v) :
    ∃ P : (toGraph (dualField ω)).Walk u v, ∀ z ∈ P.support, z = u ∨ z ∈ W := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, fun z hz => Or.inl (by simpa using hz)⟩
  | tail _ hstep ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨_, hc, hbc⟩ := hstep
    refine ⟨P.concat hbc, fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hP z hz
    · exact Or.inr hc

end

end FiniteAvalanches.Trees.Lattice
