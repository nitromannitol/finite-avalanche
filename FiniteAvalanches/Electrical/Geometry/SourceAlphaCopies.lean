import FiniteAvalanches.Electrical.Geometry.SourceAlphaBond

/-! Exact transport between retained bond copies and the original H0 alpha star. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

theorem alpha_cut_iff (D : Finset (Site 2)) (P : OneSet D) (e : PrimalCopy D P) :
    (((primalGraph D P).left e = alpha D P ∧ (primalGraph D P).right e ≠ alpha D P) ∨
      ((primalGraph D P).right e = alpha D P ∧ (primalGraph D P).left e ≠ alpha D P)) ↔
      ((primalGraph D P).left e = alpha D P ∨ (primalGraph D P).right e = alpha D P) := by
  constructor
  · exact fun h => h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · rintro (h | h)
    · exact Or.inl ⟨h, fun he => primal_loopless D P e (h.trans he.symm)⟩
    · exact Or.inr ⟨h, fun he => primal_loopless D P e (he.trans h.symm)⟩

/-- Changing singleton membership to endpoint equality preserves the original edge value. -/
def alphaSingletonCutEquiv (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    {e : PrimalCopy D P // e ≠ markedPrimal D P marked ∧
      (((primalGraph D P).left e ∈ ({alpha D P} : Finset (Vertex D P)) ∧
        (primalGraph D P).right e ∉ ({alpha D P} : Finset (Vertex D P))) ∨
      ((primalGraph D P).right e ∈ ({alpha D P} : Finset (Vertex D P)) ∧
        (primalGraph D P).left e ∉ ({alpha D P} : Finset (Vertex D P))))} ≃
    {e : PrimalCopy D P // e ≠ markedPrimal D P marked ∧
      (((primalGraph D P).left e = alpha D P ∧ (primalGraph D P).right e ≠ alpha D P) ∨
        ((primalGraph D P).right e = alpha D P ∧ (primalGraph D P).left e ≠ alpha D P))} where
  toFun e := ⟨e.val, by simpa only [Finset.mem_singleton] using e.property⟩
  invFun e := ⟨e.val, by simpa only [Finset.mem_singleton] using e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bijection is the actual unchanged original ID inclusion, restricted to the alpha cut. -/
def retainedAlphaEquiv (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    {e : PrimalCopy D P // e ≠ markedPrimal D P marked ∧
      (((primalGraph D P).left e = alpha D P ∧ (primalGraph D P).right e ≠ alpha D P) ∨
        ((primalGraph D P).right e = alpha D P ∧ (primalGraph D P).left e ≠ alpha D P))} ≃
    {e : Copy D P marked // copyA D P marked e = alpha D P ∨
      copyB D P marked e = alpha D P} where
  toFun e := ⟨⟨e.val.val, Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp e.val.property).1,
      (Finset.mem_filter.mp e.val.property).2,
      fun h => e.property.1 (Subtype.ext h)⟩⟩,
    (alpha_cut_iff D P e.val).mp e.property.2⟩
  invFun e := ⟨retainedPrimal D P marked e.val,
    retainedPrimal_ne_marked D P marked e.val, (alpha_cut_iff D P _).mpr e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem retainedAlphaEquiv_id (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P)
    (e : {e : PrimalCopy D P // e ≠ markedPrimal D P marked ∧
      (((primalGraph D P).left e = alpha D P ∧ (primalGraph D P).right e ≠ alpha D P) ∨
        ((primalGraph D P).right e = alpha D P ∧ (primalGraph D P).left e ≠ alpha D P))}) :
    retainedPrimal D P marked ((retainedAlphaEquiv D P marked e).val) = e.val := rfl

end
end FiniteAvalanches.Electrical.LatticeDrawing
