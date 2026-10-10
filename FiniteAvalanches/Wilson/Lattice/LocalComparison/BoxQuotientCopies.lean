import FiniteAvalanches.Wilson.Lattice.LocalComparison.BoxCopyIDs
import FiniteAvalanches.Trees.CopiedTreeTransport

set_option autoImplicit false
namespace LocalBoxContraction
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

abbrev BoxCopy (D : Finset (Site 2)) (P : OneSet D) (N : ℕ) :=
  CopiedNetwork.NonemptyQuotient.Copy (WiredTrees.graph N) (boxRoots D P N)
abbrev PrimalQuotientCopy (D : Finset (Site 2)) (P : OneSet D) :=
  CopiedNetwork.NonemptyQuotient.Copy (primalGraph D P) (primalRoots D P)

theorem survives_iff (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (e : FiniteWired.Edge N) :
    CopiedNetwork.NonemptyQuotient.project (boxRoots D P N) ((WiredTrees.graph N).left e) ≠
      CopiedNetwork.NonemptyQuotient.project (boxRoots D P N) ((WiredTrees.graph N).right e) ↔
    CopiedNetwork.NonemptyQuotient.project (primalRoots D P) (project D P (originalA (boxID e))) ≠
      CopiedNetwork.NonemptyQuotient.project (primalRoots D P) (project D P (originalB (boxID e))) := by
  have h := not_congr ((quotientVertexEquiv D P N hDbox).injective.eq_iff
    (a := CopiedNetwork.NonemptyQuotient.project (boxRoots D P N) ((WiredTrees.graph N).left e))
    (b := CopiedNetwork.NonemptyQuotient.project (boxRoots D P N) ((WiredTrees.graph N).right e)))
  rw [quotientVertexEquiv_project, quotientVertexEquiv_project] at h
  rcases boxID_endpoints D P N hDbox e with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · rw [hl,hr] at h
    exact h.symm
  · rw [hl,hr] at h
    exact h.symm.trans ne_comm

theorem surviving_id_mem (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (e : BoxCopy D P N) :
    boxID e.val ∈ primalCopies D P := by
  have hs := (survives_iff D P N hDbox e.val).mp e.property
  have hn : project D P (originalA (boxID e.val)) ≠ project D P (originalB (boxID e.val)) :=
    fun he => hs (congrArg (CopiedNetwork.NonemptyQuotient.project (primalRoots D P)) he)
  refine Finset.mem_filter.mpr ⟨(mem_domainCopies D _).mpr ?_, hn⟩
  by_cases ha : originalA (boxID e.val) ∈ D
  · exact Or.inl ha
  · by_cases hb : originalB (boxID e.val) ∈ D
    · exact Or.inr hb
    · exact False.elim (hn (((project_eq_alpha_iff D P _).mpr ha).trans
        ((project_eq_alpha_iff D P _).mpr hb).symm))

def quotientCopyMap (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) : BoxCopy D P N → PrimalQuotientCopy D P :=
  fun e => ⟨⟨boxID e.val, surviving_id_mem D P N hDbox e⟩,
    (survives_iff D P N hDbox e.val).mp e.property⟩

theorem quotientCopyMap_bijective (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) : Function.Bijective (quotientCopyMap D P N hDbox) := by
  constructor
  · intro e f he
    exact Subtype.ext (boxID_injective N (congrArg (fun a : PrimalQuotientCopy D P => a.val.val) he))
  · intro e
    obtain ⟨f,hf⟩ := boxID_covers_domain D N hDbox e.val.val
      (Finset.mem_filter.mp e.val.property).1
    have hs : CopiedNetwork.NonemptyQuotient.project (boxRoots D P N) ((WiredTrees.graph N).left f) ≠
        CopiedNetwork.NonemptyQuotient.project (boxRoots D P N) ((WiredTrees.graph N).right f) := by
      apply (survives_iff D P N hDbox f).mpr
      rw [hf]
      exact e.property
    exact ⟨⟨f,hs⟩, Subtype.ext (Subtype.ext hf)⟩

/-- Copies are identified by their original ID, never by their contracted endpoints. -/
def quotientCopyEquiv (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) : BoxCopy D P N ≃ PrimalQuotientCopy D P :=
  Equiv.ofBijective (quotientCopyMap D P N hDbox) (quotientCopyMap_bijective D P N hDbox)

theorem quotientCopyEquiv_id (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (e : BoxCopy D P N) :
    (quotientCopyEquiv D P N hDbox e).val.val = boxID e.val := rfl

theorem quotientCopyEquiv_endpoints (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (e : BoxCopy D P N) :
    let G := CopiedNetwork.NonemptyQuotient.graph (WiredTrees.graph N) (boxRoots D P N)
    let H := CopiedNetwork.NonemptyQuotient.graph (primalGraph D P) (primalRoots D P)
    let v := quotientVertexEquiv D P N hDbox
    let c := quotientCopyEquiv D P N hDbox
    (H.left (c e) = v (G.left e) ∧ H.right (c e) = v (G.right e)) ∨
      (H.left (c e) = v (G.right e) ∧ H.right (c e) = v (G.left e)) := by
  have hlq := quotientVertexEquiv_project D P N hDbox ((WiredTrees.graph N).left e.val)
  have hrq := quotientVertexEquiv_project D P N hDbox ((WiredTrees.graph N).right e.val)
  rcases boxID_endpoints D P N hDbox e.val with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · exact Or.inl ⟨(congrArg (CopiedNetwork.NonemptyQuotient.project (primalRoots D P)) hl).symm.trans hlq.symm,
      (congrArg (CopiedNetwork.NonemptyQuotient.project (primalRoots D P)) hr).symm.trans hrq.symm⟩
  · exact Or.inr ⟨(congrArg (CopiedNetwork.NonemptyQuotient.project (primalRoots D P)) hr).symm.trans hrq.symm,
      (congrArg (CopiedNetwork.NonemptyQuotient.project (primalRoots D P)) hl).symm.trans hlq.symm⟩

end
end LocalBoxContraction
