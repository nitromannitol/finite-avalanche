import FiniteAvalanches.Wilson.Lattice.LocalComparison.SourceColorLaw
import FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
import FiniteAvalanches.Electrical.Reference.CutConnectivity

set_option autoImplicit false
namespace LocalBoxContraction
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

abbrev boxRoots (D : Finset (Site 2)) (P : OneSet D) (N : ℕ) :=
  wiredRoots (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N

def primalRoots (D : Finset (Site 2)) (P : OneSet D) :
    CopiedNetwork.Roots (V := Vertex D P) :=
  ⟨{alpha D P, beta D P}, ⟨alpha D P, Set.mem_insert _ _⟩⟩

theorem image_mem (D : Finset (Site 2)) (P : OneSet D) (x : D) :
    x.val ∈ P.val.image Subtype.val ↔ x ∈ P.val := by
  rw [Finset.mem_image]
  exact ⟨fun ⟨y, hy, he⟩ => (Subtype.ext he) ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem box_root_some (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (x : FiniteWired.Active N) :
    some x ∈ (boxRoots D P N).val ↔
      FiniteWired.site x ∈ P.val.image Subtype.val ∨ FiniteWired.site x ∉ D := Iff.rfl

theorem box_root_none (D : Finset (Site 2)) (P : OneSet D) (N : ℕ) :
    none ∈ (boxRoots D P N).val := Or.inr trivial

def boxNonrootEquiv (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) :
    {v : FiniteWired.Vertex N // v ∉ (boxRoots D P N).val} ≃ {x : D // x ∉ P.val} where
  toFun v := by
    cases v with
    | mk v hv =>
      cases v with
      | none => exact False.elim (hv (box_root_none D P N))
      | some x =>
        have hd : FiniteWired.site x ∈ D := by
          by_contra hn
          exact hv (Or.inr hn)
        exact ⟨⟨FiniteWired.site x, hd⟩, fun hp => hv (Or.inl ((image_mem D P _).mpr hp))⟩
  invFun x := ⟨some (FiniteWired.activeOfSite N x.val.val (hDbox _ x.val.property)), by
    rw [box_root_some]
    rintro (hp | hd)
    · exact x.property ((image_mem D P x.val).mp hp)
    · exact hd x.val.property⟩
  left_inv v := by
    apply Subtype.ext
    cases v with
    | mk v hv =>
      cases v with
      | none => exact False.elim (hv (box_root_none D P N))
      | some x => exact congrArg some (FiniteWired.site_injective N rfl)
  right_inv x := rfl

def primalNonrootEquiv (D : Finset (Site 2)) (P : OneSet D) :
    {v : Vertex D P // v ∉ (primalRoots D P).val} ≃ {x : D // x ∉ P.val} where
  toFun v := by
    cases v with
    | mk v hv =>
      cases v with
      | inl b =>
        cases b
        · exact False.elim (hv (Or.inl rfl))
        · exact False.elim (hv (Or.inr (Set.mem_singleton _)))
      | inr x => exact x
  invFun x := ⟨.inr x, by simp only [primalRoots, alpha, beta, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sum.inr_ne_inl, or_self, not_false_eq_true]⟩
  left_inv v := by
    apply Subtype.ext
    cases v with
    | mk v hv =>
      cases v with
      | inl b =>
        cases b
        · exact False.elim (hv (Or.inl rfl))
        · exact False.elim (hv (Or.inr (Set.mem_singleton _)))
      | inr x => rfl
  right_inv _ := rfl

/-- The nonroot quotient vertices are precisely the original sites in D minus P. -/
def quotientVertexEquiv (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) :
    CopiedNetwork.NonemptyQuotient.Vertex (boxRoots D P N) ≃
      CopiedNetwork.NonemptyQuotient.Vertex (primalRoots D P) :=
  Equiv.optionCongr ((boxNonrootEquiv D P N hDbox).trans (primalNonrootEquiv D P).symm)

/-- Exterior roots map to alpha; original P roots map to beta. -/
def vertexMap (D : Finset (Site 2)) (P : OneSet D) (N : ℕ) :
    FiniteWired.Vertex N → Vertex D P
  | none => alpha D P
  | some x => project D P (FiniteWired.site x)

theorem vertexMap_wiredSite (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (x : Site 2) :
    vertexMap D P N (wiredSite N x) = project D P x := by
  by_cases hb : FiniteWired.inBox N x
  · rw [wiredSite, dif_pos hb]
    rfl
  · rw [wiredSite, dif_neg hb]
    exact ((project_eq_alpha_iff D P x).mpr (fun hd => hb (hDbox x hd))).symm

theorem quotientVertexEquiv_project (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (v : FiniteWired.Vertex N) :
    quotientVertexEquiv D P N hDbox (CopiedNetwork.NonemptyQuotient.project (boxRoots D P N) v) =
      CopiedNetwork.NonemptyQuotient.project (primalRoots D P) (vertexMap D P N v) := by
  cases v with
  | none =>
    simp [CopiedNetwork.NonemptyQuotient.project, box_root_none, vertexMap,
      primalRoots, quotientVertexEquiv, alpha]
    rfl
  | some x =>
    by_cases hd : FiniteWired.site x ∈ D
    · by_cases hp : (⟨FiniteWired.site x, hd⟩ : D) ∈ P.val
      · have hi := (image_mem D P _).mpr hp
        simp [CopiedNetwork.NonemptyQuotient.project, box_root_some, hi, vertexMap,
          project, hd, hp, primalRoots, beta, quotientVertexEquiv]
        rfl
      · have hi : FiniteWired.site x ∉ P.val.image Subtype.val := fun h => hp ((image_mem D P _).mp h)
        simp [CopiedNetwork.NonemptyQuotient.project, box_root_some, hi, hd, vertexMap,
          project, hp, primalRoots, alpha, beta, quotientVertexEquiv, boxNonrootEquiv,
          primalNonrootEquiv, Equiv.optionCongr]
        rfl
    · simp [CopiedNetwork.NonemptyQuotient.project, box_root_some, hd, vertexMap,
        project, primalRoots, alpha, beta, quotientVertexEquiv]
      rfl


end
end LocalBoxContraction
