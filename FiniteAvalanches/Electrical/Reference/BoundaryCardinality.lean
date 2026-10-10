import FiniteAvalanches.Electrical.Geometry.SourceAlphaCopies

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment
open LatticeProb
open scoped Classical
noncomputable section

/-- The retained alpha star has exactly the original domain-boundary count minus
its single marked original copy. No parallel copies are identified. -/
theorem retained_boundary_card (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) :
    Fintype.card {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P} =
      ((domainCopies D).filter fun e =>
        (originalA e ∈ D ∧ originalB e ∉ D) ∨
        (originalB e ∈ D ∧ originalA e ∉ D)).card - 1 := by
  let B := (domainCopies D).filter fun e =>
    (originalA e ∈ D ∧ originalB e ∉ D) ∨
    (originalB e ∈ D ∧ originalA e ∉ D)
  have hboundary (e : OriginalCopy) : e ∈ B ↔
      e ∈ domainCopies D ∧
      project D P (originalA e) ≠ project D P (originalB e) ∧
      (project D P (originalA e) = alpha D P ∨
        project D P (originalB e) = alpha D P) := by
    simp only [B, Finset.mem_filter, mem_domainCopies, project_eq_alpha_iff]
    constructor
    · rintro ⟨hd, ha | hb⟩
      · refine ⟨hd, ?_, Or.inr ha.2⟩
        intro he
        exact ((project_eq_alpha_iff D P _).mp
          (he.trans ((project_eq_alpha_iff D P _).mpr ha.2))) ha.1
      · refine ⟨hd, ?_, Or.inl hb.2⟩
        intro he
        exact ((project_eq_alpha_iff D P _).mp
          (he.symm.trans ((project_eq_alpha_iff D P _).mpr hb.2))) hb.1
    · rintro ⟨hd, _hne, hout⟩
      exact ⟨hd, by tauto⟩
  have hmarked : marked.val ∈ B := by
    apply (hboundary _).mpr
    have hab : alpha D P ≠ beta D P := by intro h; cases h
    rcases marked.property with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · refine ⟨(mem_domainCopies D _).mpr (Or.inr ?_), ?_, Or.inl ha⟩
      · obtain ⟨x, _hx, he⟩ := Finset.mem_image.mp ((project_eq_beta_iff D P _).mp hb)
        exact he ▸ x.property
      · rw [ha, hb]; exact hab
    · refine ⟨(mem_domainCopies D _).mpr (Or.inl ?_), ?_, Or.inr ha⟩
      · obtain ⟨x, _hx, he⟩ := Finset.mem_image.mp ((project_eq_beta_iff D P _).mp hb)
        exact he ▸ x.property
      · rw [hb, ha]; exact hab.symm
  let e : {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P} ≃
      ↥(B.erase marked.val) :=
    { toFun := fun x => ⟨x.val.val, Finset.mem_erase.mpr
        ⟨(Finset.mem_filter.mp x.val.property).2.2,
          (hboundary _).mpr ⟨(Finset.mem_filter.mp x.val.property).1,
            (Finset.mem_filter.mp x.val.property).2.1, x.property⟩⟩⟩
      invFun := fun x =>
        let hx := (hboundary _).mp (Finset.mem_erase.mp x.property).2
        ⟨⟨x.val, Finset.mem_filter.mpr
          ⟨hx.1, hx.2.1, (Finset.mem_erase.mp x.property).1⟩⟩, hx.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_erase_of_mem hmarked]

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment
