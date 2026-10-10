import FiniteAvalanches.Electrical.Reference.CutConnectivity

/-! Erasing one copied edge preserves connectedness of H and H0. -/

namespace FiniteAvalanches.Electrical.Plane.SourceLattice

open LatticeProb
open scoped Classical
noncomputable section

theorem retainedCopies_eq_primal_erase (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) :
    retainedCopies D P marked = (primalCopies D P).erase marked.val := by
  ext e
  simp only [retainedCopies, primalCopies, Finset.mem_filter, Finset.mem_erase]
  tauto

/-- The actual H0 cut loses exactly the marked original ID. -/
def retainedCut (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (U : Finset (Vertex D P)) : Finset OriginalCopy :=
  (retainedCopies D P marked).filter fun e =>
    (project D P (originalA e) ∈ U ∧ project D P (originalB e) ∉ U) ∨
    (project D P (originalB e) ∈ U ∧ project D P (originalA e) ∉ U)

theorem retainedCut_eq_erase (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (U : Finset (Vertex D P)) :
    retainedCut D P marked U = (quotientCut D P U).erase marked.val := by
  ext e
  simp only [retainedCut, quotientCut, retainedCopies_eq_primal_erase,
    Finset.mem_filter, Finset.mem_erase]
  tauto

/-- Three copy-distinct exits remain in every nonempty H0 cut away from alpha. -/
theorem retainedCut_card_ge_three (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (U : Finset (Vertex D P))
    (ha : alpha D P ∉ U) (hU : U.Nonempty) :
    3 ≤ (retainedCut D P marked U).card := by
  rw [retainedCut_eq_erase]
  have hfour := quotientCut_card_ge_four D P U ha hU
  have hpred := Finset.pred_card_le_card_erase (a := marked.val) (s := quotientCut D P U)
  omega

/-- No bridge in H: deleting one literal copied edge leaves every pair connected. -/
theorem primal_reaches_erase (D : Finset (Site 2)) (P : OneSet D)
    (e : PrimalCopy D P) (x y : Vertex D P) :
    (primalGraph D P).reaches (Finset.univ.erase e) x y := by
  have hs : primalSurviving D P {e.val} = Finset.univ.erase e := by
    ext c
    simp only [primalSurviving, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Finset.mem_erase, and_true, Subtype.val_inj]
  rw [← hs]
  exact primal_reaches_of_deleted_card_le_three D P {e.val} (by simp) x y

/-- No bridge in the actual H0 carrier: only the selected copied edge is erased. -/
theorem graph_reaches_erase (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (e : Copy D P marked) (x y : Vertex D P) :
    (StatementTypes.graph D P marked).reaches (Finset.univ.erase e) x y := by
  have hd : ({marked.val,e.val} : Finset OriginalCopy).card ≤ 3 :=
    Finset.card_le_two.trans (by decide)
  have hr := primal_reaches_of_deleted_card_le_three D P {marked.val,e.val} hd x y
  induction hr with
  | refl => exact .refl
  | @tail u v _ hadj ih =>
    obtain ⟨c,hc,hends⟩ := hadj
    have hn : c.val ≠ marked.val ∧ c.val ≠ e.val := by
      have hh := (Finset.mem_filter.mp hc).2
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hh
    let c' : Copy D P marked := ⟨c.val, by
      rw [retainedCopies_eq_primal_erase, Finset.mem_erase]
      exact ⟨hn.1,c.property⟩⟩
    have hc' : c' ∈ (Finset.univ : Finset (Copy D P marked)).erase e := by
      apply Finset.mem_erase.mpr
      exact ⟨fun h => hn.2 (congrArg Subtype.val h),Finset.mem_univ _⟩
    exact ih.trans (.single ⟨c',hc',hends⟩)

end
end FiniteAvalanches.Electrical.Plane.SourceLattice
