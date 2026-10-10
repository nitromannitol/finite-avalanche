import FiniteAvalanches.Wilson.Lattice.LocalComparison.BoxQuotientCopies

set_option autoImplicit false
namespace LocalBoxContraction
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Electrical.Plane.SourceLattice
open CopiedNetwork.NonemptyQuotient (rootContractionEquiv projectCopies liftCopies lift_project_forest)
open scoped Classical
noncomputable section

local instance primalDecidableEq (D : Finset (Site 2)) (P : OneSet D) : DecidableEq (PrimalCopy D P) :=
  Classical.decEq _

abbrev PrimalForest (D : Finset (Site 2)) (P : OneSet D) :=
  (primalGraph D P).RootedForest ({alpha D P, beta D P} : Set (Vertex D P))

def quotientTreeEquiv (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) :
    (CopiedNetwork.NonemptyQuotient.graph (WiredTrees.graph N) (boxRoots D P N)).ComponentTree Set.univ ≃
      (CopiedNetwork.NonemptyQuotient.graph (primalGraph D P) (primalRoots D P)).ComponentTree Set.univ where
  toFun t := ⟨t.val.image (quotientCopyEquiv D P N hDbox),
    (Multigraph.copiedEquiv_tree_iff _ _ (quotientVertexEquiv D P N hDbox)
      (quotientCopyEquiv D P N hDbox) (quotientCopyEquiv_endpoints D P N hDbox) t.val).mpr t.property⟩
  invFun t := ⟨t.val.image (quotientCopyEquiv D P N hDbox).symm, by
    apply (Multigraph.copiedEquiv_tree_iff _ _ (quotientVertexEquiv D P N hDbox)
      (quotientCopyEquiv D P N hDbox) (quotientCopyEquiv_endpoints D P N hDbox) _).mp
    simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply,
      Finset.image_id'] using t.property⟩
  left_inv t := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply, Finset.image_id']
  right_inv t := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id']

/-- Bijection on the entire original box and source primal rooted-forest carriers. -/
def forestEquiv (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) :
    FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N ≃ PrimalForest D P :=
  (rootContractionEquiv (WiredTrees.graph N) (boxRoots D P N)).trans
    ((quotientTreeEquiv D P N hDbox).trans
      (rootContractionEquiv (primalGraph D P) (primalRoots D P)).symm)

theorem forestEquiv_left_inv (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N) :
    (forestEquiv D P N hDbox).symm (forestEquiv D P N hDbox F) = F :=
  (forestEquiv D P N hDbox).symm_apply_apply F

theorem forestEquiv_right_inv (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (F : PrimalForest D P) :
    forestEquiv D P N hDbox ((forestEquiv D P N hDbox).symm F) = F :=
  (forestEquiv D P N hDbox).apply_symm_apply F

/-- Both forest subsets retain exactly the same original copied-edge IDs. -/
theorem forestEquiv_original_ids (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N) :
    (forestEquiv D P N hDbox F).val.image Subtype.val = F.val.image boxID := by
  change (liftCopies (primalGraph D P) (primalRoots D P)
    ((projectCopies (WiredTrees.graph N) (boxRoots D P N) F.val).image
      (quotientCopyEquiv D P N hDbox))).image Subtype.val = _
  calc
    _ = (liftCopies (WiredTrees.graph N) (boxRoots D P N)
        (projectCopies (WiredTrees.graph N) (boxRoots D P N) F.val)).image boxID := by
      simp only [liftCopies, Finset.image_image, Function.comp_def, quotientCopyEquiv_id]
    _ = F.val.image boxID := by rw [lift_project_forest _ _ F.property]

theorem full_denominator (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) :
    finiteForestCount (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N =
      Nat.card (PrimalForest D P) := Nat.card_congr (forestEquiv D P N hDbox)

/-- Every selected original step survives with its two correctly grouped endpoints. -/
theorem adjacent_map (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N)
    {x y : FiniteWired.Vertex N} (h : (WiredTrees.graph N).adjacent F.val x y) :
    (primalGraph D P).adjacent (forestEquiv D P N hDbox F).val
      (vertexMap D P N x) (vertexMap D P N y) := by
  obtain ⟨e,he,hxy⟩ := h
  have hi : boxID e ∈ (forestEquiv D P N hDbox F).val.image Subtype.val := by
    rw [forestEquiv_original_ids]
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩
  obtain ⟨c,hc,hce⟩ := Finset.mem_image.mp hi
  refine ⟨c,hc,?_⟩
  have ha : (primalGraph D P).left c = project D P (originalA (boxID e)) := congrArg (fun a : OriginalCopy => project D P (originalA a)) hce
  have hb : (primalGraph D P).right c = project D P (originalB (boxID e)) := congrArg (fun a : OriginalCopy => project D P (originalB a)) hce
  rcases boxID_endpoints D P N hDbox e with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · rcases hxy with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact Or.inl ⟨ha.trans (hl.symm.trans (congrArg _ hx)), hb.trans (hr.symm.trans (congrArg _ hy))⟩
    · exact Or.inr ⟨hb.trans (hr.symm.trans (congrArg _ hx)), ha.trans (hl.symm.trans (congrArg _ hy))⟩
  · rcases hxy with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact Or.inr ⟨hb.trans (hl.symm.trans (congrArg _ hx)), ha.trans (hr.symm.trans (congrArg _ hy))⟩
    · exact Or.inl ⟨ha.trans (hr.symm.trans (congrArg _ hx)), hb.trans (hl.symm.trans (congrArg _ hy))⟩

theorem reaches_map (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N)
    {x y : FiniteWired.Vertex N} (h : (WiredTrees.graph N).reaches F.val x y) :
    (primalGraph D P).reaches (forestEquiv D P N hDbox F).val
      (vertexMap D P N x) (vertexMap D P N y) :=
  Relation.ReflTransGen.lift' (vertexMap D P N)
    (fun _ _ hxy => Relation.ReflTransGen.single (adjacent_map D P N hDbox F hxy)) _ _ h

end
end LocalBoxContraction
