import FiniteAvalanches.Electrical.Reference.NoBridges

/-! Cut bounds and copied-edge deletion connectivity in the actual wired quotient. -/

namespace FiniteAvalanches.Electrical.Plane.SourceLattice

open LatticeProb
open scoped Classical
noncomputable section

/-- H retains every original ID incident to D except contraction loops. -/
def primalCopies (D : Finset (Site 2)) (P : OneSet D) : Finset OriginalCopy :=
  (domainCopies D).filter fun e =>
    project D P (originalA e) ≠ project D P (originalB e)

abbrev PrimalCopy (D : Finset (Site 2)) (P : OneSet D) := ↥(primalCopies D P)

/-- The pre-marked-deletion multigraph H, on the same quotient vertices as H0. -/
def primalGraph (D : Finset (Site 2)) (P : OneSet D) :
    Trees.Multigraph (Vertex D P) (PrimalCopy D P) where
  left e := project D P (originalA e.val)
  right e := project D P (originalB e.val)
  loopless e := (Finset.mem_filter.mp e.property).2

/-- Cut copies are indexed by original IDs, preserving parallel multiplicity. -/
def quotientCut (D : Finset (Site 2)) (P : OneSet D) (U : Finset (Vertex D P)) :
    Finset OriginalCopy :=
  (primalCopies D P).filter fun e =>
    (project D P (originalA e) ∈ U ∧ project D P (originalB e) ∉ U) ∨
    (project D P (originalB e) ∈ U ∧ project D P (originalA e) ∉ U)

/-- The finite lattice preimage of the side away from the exterior terminal. -/
def cutPreimage (D : Finset (Site 2)) (P : OneSet D) (U : Finset (Vertex D P)) :
    Finset (Site 2) := D.filter fun x => project D P x ∈ U

theorem mem_cutPreimage (D : Finset (Site 2)) (P : OneSet D)
    (U : Finset (Vertex D P)) (ha : alpha D P ∉ U) (x : Site 2) :
    x ∈ cutPreimage D P U ↔ project D P x ∈ U := by
  rw [cutPreimage, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hx
    refine ⟨?_,hx⟩
    by_contra hn
    have he := (project_eq_alpha_iff D P x).mpr hn
    exact ha (he ▸ hx)

theorem cutPreimage_nonempty (D : Finset (Site 2)) (P : OneSet D)
    (U : Finset (Vertex D P)) (ha : alpha D P ∉ U) (hU : U.Nonempty) :
    (cutPreimage D P U).Nonempty := by
  obtain ⟨v,hv⟩ := hU
  cases v with
  | inl b => cases b with
    | false => exact (ha hv).elim
    | true =>
      obtain ⟨p,hp⟩ := P.property
      have he : project D P p.val = beta D P :=
        (project_eq_beta_iff D P _).mpr (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
      exact ⟨p.val, (mem_cutPreimage D P U ha _).mpr (he.symm ▸ hv)⟩
  | inr x =>
    exact ⟨x.val.val, (mem_cutPreimage D P U ha _).mpr
      ((project_free D P x).symm ▸ hv)⟩

/-- Every lifted exit crosses the quotient cut and therefore is not a loop. -/
theorem latticeExits_cutPreimage_subset (D : Finset (Site 2)) (P : OneSet D)
    (U : Finset (Vertex D P)) (ha : alpha D P ∉ U) :
    latticeExits (cutPreimage D P U) ⊆ quotientCut D P U := by
  intro e he
  have hex := (mem_latticeExits _ e).mp he
  rw [quotientCut, Finset.mem_filter]
  have hcross :
      (project D P (originalA e) ∈ U ∧ project D P (originalB e) ∉ U) ∨
      (project D P (originalB e) ∈ U ∧ project D P (originalA e) ∉ U) := by
    simpa only [mem_cutPreimage D P U ha] using hex
  refine ⟨?_,hcross⟩
  rw [primalCopies, Finset.mem_filter, mem_domainCopies]
  constructor
  · rcases hex with h | h
    · exact Or.inl (Finset.mem_filter.mp h.1).1
    · exact Or.inr (Finset.mem_filter.mp h.1).1
  · intro h
    rcases hcross with hcross | hcross
    · exact hcross.2 (h ▸ hcross.1)
    · exact hcross.2 (h.symm ▸ hcross.1)

/-- Every nonempty quotient cut away from alpha has at least four original copies. -/
theorem quotientCut_card_ge_four (D : Finset (Site 2)) (P : OneSet D)
    (U : Finset (Vertex D P)) (ha : alpha D P ∉ U) (hU : U.Nonempty) :
    4 ≤ (quotientCut D P U).card :=
  (latticeExits_card_ge_four _ (cutPreimage_nonempty D P U ha hU)).trans
    (Finset.card_le_card (latticeExits_cutPreimage_subset D P U ha))

/-- Delete original IDs, rather than undirected endpoint pairs. -/
def primalSurviving (D : Finset (Site 2)) (P : OneSet D)
    (deleted : Finset OriginalCopy) : Finset (PrimalCopy D P) :=
  Finset.univ.filter fun e => e.val ∉ deleted

/-- Wiring any finite lattice set stays connected after deletion of at most three IDs. -/
theorem primal_reaches_of_deleted_card_le_three (D : Finset (Site 2)) (P : OneSet D)
    (deleted : Finset OriginalCopy) (hd : deleted.card ≤ 3) (x y : Vertex D P) :
    (primalGraph D P).reaches (primalSurviving D P deleted) x y := by
  let G := primalGraph D P
  let s := primalSurviving D P deleted
  have hr (v : Vertex D P) : G.reaches s (alpha D P) v := by
    by_contra hv
    let U : Finset (Vertex D P) := Finset.univ.filter fun v =>
      ¬G.reaches s (alpha D P) v
    have ha : alpha D P ∉ U := by
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      exact Relation.ReflTransGen.refl
    have hU : U.Nonempty := ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩
    have hsub : quotientCut D P U ⊆ deleted := by
      intro e he
      by_contra hed
      obtain ⟨hep,hcross⟩ := Finset.mem_filter.mp he
      let c : PrimalCopy D P := ⟨e,hep⟩
      have hc : c ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hed⟩
      have hedge : G.reaches s (project D P (originalA e))
          (project D P (originalB e)) :=
        .single ⟨c,hc,Or.inl ⟨rfl,rfl⟩⟩
      have hu (z : Vertex D P) : z ∈ U ↔ ¬G.reaches s (alpha D P) z := by
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hcross with ⟨hA,hB⟩ | ⟨hB,hA⟩
      · have hb : G.reaches s (alpha D P) (project D P (originalB e)) := by
          by_contra hh
          exact hB ((hu _).mpr hh)
        exact (hu _).mp hA (hb.trans (G.reaches_symm hedge))
      · have ha' : G.reaches s (alpha D P) (project D P (originalA e)) := by
          by_contra hh
          exact hA ((hu _).mpr hh)
        exact (hu _).mp hB (ha'.trans hedge)
    have hfour := quotientCut_card_ge_four D P U ha hU
    have hle := Finset.card_le_card hsub
    omega
  exact (G.reaches_symm (hr x)).trans (hr y)

end
end FiniteAvalanches.Electrical.Plane.SourceLattice
