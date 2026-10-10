import FiniteAvalanches.Electrical.Reference.ForestCompletion

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section
local instance dictionaryPrimalDec (D : Finset (Site 2)) (P : OneSet D) :
    DecidableEq (PrimalCopy D P) := Classical.decEq _
local instance dictionaryCopyDec (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) := Classical.decEq _
variable (hstandard : (∀ {V E : Type} [finiteV : Fintype V] [finiteE : Fintype E]
    (G : FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph V E)
    (Q : @FiniteAvalanches.Electrical.StatementGeometry.Drawing V E finiteV finiteE G)
    (charts : ∀ e, FiniteAvalanches.Electrical.Source.EdgeChart Q e),
  (Set.univ : Set V).Nonempty →
  (∀ x y, G.reaches Finset.univ x y) →
  ∀ finiteFaces : Fintype (FiniteAvalanches.Electrical.BSST.Face Q),
    letI : Fintype (FiniteAvalanches.Electrical.BSST.Face Q) := finiteFaces
    ∀ S : Finset E,
      ((Set.univ : Set V).Nonempty ∧ (∀ x y, G.reaches S x y) ∧
        ∀ e ∈ S, ¬G.reaches (S.erase e) (G.left e) (G.right e)) ↔
      ((Set.univ : Set (FiniteAvalanches.Electrical.BSST.Face Q)).Nonempty ∧
        (∀ x y, (⟨fun e => FiniteAvalanches.Electrical.BSST.negativeChartFace Q e (charts e),
          fun e => FiniteAvalanches.Electrical.BSST.positiveChartFace Q e (charts e)⟩ :
          FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
            (FiniteAvalanches.Electrical.BSST.Face Q) E).reaches Sᶜ x y) ∧
        ∀ e ∈ Sᶜ, ¬(⟨fun e => FiniteAvalanches.Electrical.BSST.negativeChartFace Q e (charts e),
          fun e => FiniteAvalanches.Electrical.BSST.positiveChartFace Q e (charts e)⟩ :
          FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
            (FiniteAvalanches.Electrical.BSST.Face Q) E).reaches
          (Sᶜ.erase e)
          (FiniteAvalanches.Electrical.BSST.negativeChartFace Q e (charts e))
          (FiniteAvalanches.Electrical.BSST.positiveChartFace Q e (charts e)))))

include hstandard

/-- The whole actual forest predicate is precisely the actual deleted-dual tree predicate
on the complementary original copies, conditional on generic plane tree complementation. -/
theorem source_forest_dual_iff (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ F : Finset (Copy D P marked),
    (StatementTypes.graph D P marked).is_rooted_forest
      ({alpha D P, beta D P} : Set (Vertex D P)) F ↔
    ((Set.univ : Set (Face Q)).Nonempty ∧
      (∀ x y, (sourceDeletedDualGraph D P marked Q charts).reaches Fᶜ x y) ∧
      ∀ e ∈ Fᶜ, ¬(sourceDeletedDualGraph D P marked Q charts).reaches
        (Fᶜ.erase e) ((sourceDeletedDualGraph D P marked Q charts).left e)
        ((sourceDeletedDualGraph D P marked Q charts).right e)) := by
  letI : Fintype (Face Q) := finiteFaces
  intro F
  have hc := hstandard (primalGraph D P) Q charts
    ⟨alpha D P, Set.mem_univ _⟩ (primal_reaches_of_domain_connected D P hD marked)
    finiteFaces (insert (markedPrimal D P marked) (F.image (retainedPrimal D P marked)))
  rw [source_completion_complement] at hc
  exact (source_forest_completion_iff D P marked F).trans
    (hc.trans (CopiedGraph.tree_image_iff (sourceDualGraph D P Q charts)
      (sourceDeletedDualGraph D P marked Q charts) (retainedPrimal D P marked)
      (retainedPrimal_injective D P marked) (fun _ => rfl) (fun _ => rfl) Fᶜ))

/-- Original absent copies, with full forest and tree carriers and literal inverse complement. -/
def sourceForestDualEquiv (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ReferenceMoment.Forest D P marked ≃ (sourceDeletedDualGraph D P marked Q charts).SpanningTree := by
  letI : Fintype (Face Q) := finiteFaces
  let iff := source_forest_dual_iff hstandard D P hD marked Q charts finiteFaces
  exact {
    toFun := fun F => ⟨F.valᶜ, (iff F.val).mp F.property⟩
    invFun := fun T => ⟨T.valᶜ, (iff T.valᶜ).mpr (by
      simpa only [compl_compl] using T.property)⟩
    left_inv := fun F => Subtype.ext (compl_compl F.val)
    right_inv := fun T => Subtype.ext (compl_compl T.val) }

/-- The selected dual IDs are exactly the original absent H0 IDs. -/
theorem sourceForestDualEquiv_copies (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ F : ReferenceMoment.Forest D P marked,
      (sourceForestDualEquiv hstandard D P hD marked Q charts finiteFaces F).val = F.valᶜ := by
  intro F
  rfl

/-- Beta color at the other endpoint of an original boundary copy is exactly use of
that same dual copy on the path between the original marked dual endpoints. -/
theorem source_boundary_color_path (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ (F : ReferenceMoment.Forest D P marked) (e : Copy D P marked) (x : Vertex D P),
      ((copyA D P marked e = alpha D P ∧ copyB D P marked e = x) ∨
        (copyB D P marked e = alpha D P ∧ copyA D P marked e = x)) →
      (if (StatementTypes.graph D P marked).reaches F.val x (beta D P)
        then (1 : ℝ) else 0) =
      (sourceDeletedDualGraph D P marked Q charts).pathIndicator
        (sourceForestDualEquiv hstandard D P hD marked Q charts finiteFaces F)
        ((sourceDualGraph D P Q charts).left (markedPrimal D P marked))
        ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) e := by
  letI : Fintype (Face Q) := finiteFaces
  intro F e x hends
  let G := StatementTypes.graph D P marked
  let K : CopiedGraph (Vertex D P) (Copy D P marked) :=
    ⟨copyA D P marked, copyB D P marked⟩
  let J := sourceDeletedDualGraph D P marked Q charts
  let H := sourceDualGraph D P Q charts
  let f := retainedPrimal D P marked
  let z := markedPrimal D P marked
  let equiv := sourceForestDualEquiv hstandard D P hD marked Q charts finiteFaces
  have color : G.reaches F.val x (beta D P) ↔
      ¬K.reaches F.val (copyA D P marked e) (copyB D P marked e) := by
    rcases hends with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rw [ha, hb]
      exact source_forest_beta_iff D P marked F x
    · rw [ha, hb]
      exact (source_forest_beta_iff D P marked F x).trans
        (not_congr ⟨fun h => CopiedGraph.TwoCopy.reaches_symm K h,
          fun h => CopiedGraph.TwoCopy.reaches_symm K h⟩)
  by_cases he : e ∈ F.val
  · have hc : ¬G.reaches F.val x (beta D P) := fun h =>
      (color.mp h) (.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
    have hd : e ∉ (equiv F).val := by
      change e ∉ F.valᶜ
      exact Finset.notMem_compl.mpr he
    rw [if_neg hc, CopiedGraph.pathIndicator, if_neg (fun h => hd h.1)]
  · have hnz : z ∉ F.val.image f := by
      rintro hz
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hz
      exact retainedPrimal_ne_marked D P marked a ha
    let T : (primalGraph D P).SpanningTree :=
      ⟨insert z (F.val.image f), (source_forest_completion_iff D P marked F.val).mp F.property⟩
    let U : H.SpanningTree := ⟨F.valᶜ.image f,
      (CopiedGraph.tree_image_iff H J f (retainedPrimal_injective D P marked)
        (fun _ => rfl) (fun _ => rfl) F.valᶜ).mpr (equiv F).property⟩
    have hU : U.val = T.valᶜ := (source_completion_complement D P marked F.val).symm
    have hnot : f e ∉ T.val := by
      rintro ht
      rcases Finset.mem_insert.mp ht with hz | ht
      · exact retainedPrimal_ne_marked D P marked e hz
      · obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp ht
        exact he ((retainedPrimal_injective D P marked hae) ▸ ha)
    have hh := CopiedGraph.complement_exchange (primalGraph D P) H
      (hstandard (primalGraph D P) Q charts ⟨alpha D P, Set.mem_univ _⟩
        (primal_reaches_of_domain_connected D P hD marked) finiteFaces)
      T U hU z (f e) (Finset.mem_insert_self _ _) hnot
    have hte : T.val.erase z = F.val.image f := Finset.erase_insert hnz
    have hue : U.val.erase (f e) = (F.valᶜ.erase e).image f :=
      (Finset.image_erase (retainedPrimal_injective D P marked) F.valᶜ e).symm
    rw [hte, hue] at hh
    have rp := CopiedGraph.reaches_image_iff (primalGraph D P) K f
      (fun _ => rfl) (fun _ => rfl) F.val (copyA D P marked e) (copyB D P marked e)
    have rd := CopiedGraph.reaches_image_iff H J f (fun _ => rfl) (fun _ => rfl)
      (F.valᶜ.erase e) (H.left z) (H.right z)
    have event : G.reaches F.val x (beta D P) ↔
        ¬J.reaches (F.valᶜ.erase e) (H.left z) (H.right z) :=
      color.trans ((not_congr rp).symm.trans (hh.trans (not_congr rd)))
    change (if G.reaches F.val x (beta D P) then (1 : ℝ) else 0) =
      (if e ∈ F.valᶜ ∧ ¬J.reaches (F.valᶜ.erase e) (H.left z) (H.right z) then 1 else 0)
    rw [propext event]
    simp only [Finset.mem_compl.mpr he, true_and]
    split_ifs <;> rfl

/-- Uniform means use the entire actual carriers, under any enumeration of the dual trees. -/
theorem source_forest_uniform_mean (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ treeEnumeration : Fintype (sourceDeletedDualGraph D P marked Q charts).SpanningTree,
    letI := treeEnumeration
    ∀ a : ReferenceMoment.Forest D P marked → ℝ,
      (∑ F : ReferenceMoment.Forest D P marked, a F) /
        (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) =
      (∑ T : (sourceDeletedDualGraph D P marked Q charts).SpanningTree,
        a ((sourceForestDualEquiv hstandard D P hD marked Q charts finiteFaces).symm T)) /
        (Fintype.card (sourceDeletedDualGraph D P marked Q charts).SpanningTree : ℝ) := by
  letI : Fintype (Face Q) := finiteFaces
  intro treeEnumeration
  letI := treeEnumeration
  intro a
  let equiv := sourceForestDualEquiv hstandard D P hD marked Q charts finiteFaces
  have hs := (equiv.symm.sum_comp a).symm
  rw [hs, Fintype.card_congr equiv]
end
end FiniteAvalanches.Electrical.LatticeDrawing
