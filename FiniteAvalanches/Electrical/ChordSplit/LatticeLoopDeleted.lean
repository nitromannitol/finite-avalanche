import FiniteAvalanches.Electrical.ChordSplit.LoopDeletedResponse
import FiniteAvalanches.Electrical.ChordSplit.LatticeCopiedGraph
import FiniteAvalanches.Electrical.Plane.SplitFormation

/-! Loop deletion and total conductance on the actual original lattice copies. -/
namespace ElectricalFollowup.LoopDeletion
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.ChordSplit FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.Plane FiniteAvalanches.Electrical.Plane.SourceLattice
open LatticeProb
open scoped Classical
noncomputable section

variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (side : Copy D P marked → Bool)

/-- The identified image of a genuine interior site. -/
def interiorGround (x : D) : GroundedSplitVertex (alpha D P) (beta D P) :=
  groundMap (alpha D P) (beta D P) (.inl ⟨project D P x.val,
    fun h => ((project_eq_alpha_iff D P _).mp h) x.property⟩)

private theorem endpoint_interior (x : D) (e : Copy D P marked)
    (hx : copyA D P marked e = project D P x.val) :
    (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
      (alpha D P) (beta D P) side).left e = interiorGround D P x := by
  have hn : project D P x.val ≠ alpha D P :=
    fun h => ((project_eq_alpha_iff D P _).mp h) x.property
  simp only [groundedSplitGraph,splitGraph,Canonical.latticeCopiedGraph,splitEndpoint,hx,dif_neg hn]
  rfl

private theorem endpoint_interior_right (x : D) (e : Copy D P marked)
    (hx : copyB D P marked e = project D P x.val) :
    (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
      (alpha D P) (beta D P) side).right e = interiorGround D P x := by
  have hn : project D P x.val ≠ alpha D P :=
    fun h => ((project_eq_alpha_iff D P _).mp h) x.property
  simp only [groundedSplitGraph,splitGraph,Canonical.latticeCopiedGraph,splitEndpoint,hx,dif_neg hn]
  rfl

private theorem internal_copy_reaches (e : OriginalCopy)
    (ha : originalA e ∈ D) (hb : originalB e ∈ D) :
    (supportGraph (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
      (alpha D P) (beta D P) side).left
      (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
        (alpha D P) (beta D P) side).right).Reachable
      (interiorGround D P ⟨originalA e,ha⟩) (interiorGround D P ⟨originalB e,hb⟩) := by
  by_cases heq : project D P (originalA e) = project D P (originalB e)
  · have h : interiorGround D P ⟨originalA e,ha⟩ = interiorGround D P ⟨originalB e,hb⟩ :=
      congrArg (groundMap (alpha D P) (beta D P)) (congrArg Sum.inl (Subtype.ext heq))
    rw [h]
  · let c : Copy D P marked := ⟨e,(mem_retainedCopies D P marked e).mpr
      ⟨Or.inl ha,heq,Repair8.internal_ne_marked D P marked e ha hb⟩⟩
    have hl := endpoint_interior D P marked side ⟨originalA e,ha⟩ c rfl
    have hr := endpoint_interior_right D P marked side ⟨originalB e,hb⟩ c rfl
    by_cases hxy : interiorGround D P ⟨originalA e,ha⟩ = interiorGround D P ⟨originalB e,hb⟩
    · rw [hxy]
    · exact SimpleGraph.Adj.reachable ⟨hxy,c,Or.inl ⟨hl,hr⟩⟩

private theorem internal_adj_reaches (x y : D)
    (hxy : ((lattice 2).induce (↑D : Set (Site 2))).Adj x y) :
    (supportGraph (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
      (alpha D P) (beta D P) side).left
      (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
        (alpha D P) (beta D P) side).right).Reachable
      (interiorGround D P x) (interiorGround D P y) := by
  change ∃ i : Fin 2, y.val = x.val + unit i ∨ x.val = y.val + unit i at hxy
  obtain ⟨i,h | h⟩ := hxy
  · have hyD : originalB (x.val,i) ∈ D := by
      change x.val + unit i ∈ D
      rw [← h]
      exact y.property
    have hy : y = (⟨x.val + unit i,hyD⟩ : D) := Subtype.ext h
    rw [hy]
    exact internal_copy_reaches D P marked side (x.val,i) x.property hyD
  · have hxD : originalB (y.val,i) ∈ D := by
      change y.val + unit i ∈ D
      rw [← h]
      exact x.property
    have hx : x = (⟨y.val + unit i,hxD⟩ : D) := Subtype.ext h
    rw [hx]
    exact (internal_copy_reaches D P marked side (y.val,i) y.property hxD).symm

theorem interior_reaches_ground
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (x : D) :
    (supportGraph (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
      (alpha D P) (beta D P) side).left
      (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
        (alpha D P) (beta D P) side).right).Reachable (interiorGround D P x) (.inr false) := by
  obtain ⟨p,hp⟩ := P.property
  have hbp : project D P p.val = beta D P :=
    (project_eq_beta_iff D P _).mpr (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  have hground : interiorGround D P p = .inr false := by
    simp only [interiorGround,groundMap,dif_pos hbp]
  have lift {u v : D} (w : ((lattice 2).induce (↑D : Set (Site 2))).Walk u v) :
      (supportGraph (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
        (alpha D P) (beta D P) side).left
        (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
          (alpha D P) (beta D P) side).right).Reachable
        (interiorGround D P u) (interiorGround D P v) := by
    induction w with
    | nil => exact .rfl
    | cons h _ ih => exact (internal_adj_reaches D P marked side _ _ h).trans ih
  obtain ⟨w⟩ := hD.preconnected x p
  exact hground ▸ lift w

/-- A proper suffix supplies its original incident copy. Interior connectivity
then proves connectedness of the retained identified graph. -/
theorem grounded_preconnected
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hsuffix : ∃ e, splitEndpoint (alpha D P) side (copyA D P marked e) e = .inr true ∨
      splitEndpoint (alpha D P) side (copyB D P marked e) e = .inr true) :
    (supportGraph (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
      (alpha D P) (beta D P) side).left
      (groundedSplitGraph (Canonical.latticeCopiedGraph D P marked)
        (alpha D P) (beta D P) side).right).Preconnected := by
  let K := groundedSplitGraph (Canonical.latticeCopiedGraph D P marked) (alpha D P) (beta D P) side
  have hinterior (v : {v : Vertex D P // v ≠ alpha D P}) :
      (supportGraph K.left K.right).Reachable (groundMap (alpha D P) (beta D P) (.inl v)) (.inr false) := by
    rcases v with ⟨v,hv⟩
    cases v with
    | inl b =>
      cases b
      · exact (hv rfl).elim
      · change (supportGraph K.left K.right).Reachable
          (groundMap (alpha D P) (beta D P) (.inl ⟨beta D P,hv⟩)) (.inr false)
        rw [groundMap_beta]
    | inr x =>
      simpa only [interiorGround,project_free] using
        interior_reaches_ground D P marked side hD x.val
  have htrue : (supportGraph K.left K.right).Reachable (.inr true) (.inr false) := by
    obtain ⟨e,he⟩ := hsuffix
    have hedge : (supportGraph K.left K.right).Reachable (K.left e) (K.right e) := by
      by_cases heq : K.left e = K.right e
      · rw [heq]
      · exact SimpleGraph.Adj.reachable ⟨heq,e,Or.inl ⟨rfl,rfl⟩⟩
    have hlink {a b : Vertex D P}
        (hloop : a ≠ b) (hs : splitEndpoint (alpha D P) side a e = .inr true)
        (hr : (supportGraph K.left K.right).Reachable
          (groundMap (alpha D P) (beta D P) (splitEndpoint (alpha D P) side a e))
          (groundMap (alpha D P) (beta D P) (splitEndpoint (alpha D P) side b e))) :
        (supportGraph K.left K.right).Reachable (.inr true) (.inr false) := by
      have halpha : a = alpha D P := by
        unfold splitEndpoint at hs
        split_ifs at hs with h
        exact h
      have hbne : b ≠ alpha D P := fun h => hloop (halpha.trans h.symm)
      rw [hs,groundMap_alpha,splitEndpoint,dif_neg hbne] at hr
      exact hr.trans (hinterior ⟨b,hbne⟩)
    rcases he with he | he
    · exact hlink (copy_loopless D P marked e) he hedge
    · exact hlink (copy_loopless D P marked e).symm he hedge.symm
  have hreach (x : GroundedSplitVertex (alpha D P) (beta D P)) :
      (supportGraph K.left K.right).Reachable x (.inr false) := by
    cases x with
    | inl x =>
      have hx := hinterior ⟨x.val,x.property.1⟩
      simpa only [groundMap,dif_neg x.property.2] using hx
    | inr b => cases b
               · exact .rfl
               · exact htrue
  exact fun x y => (hreach x).trans (hreach y).symm

/-- Exact total conductance on the actual lattice carrier, with connectivity
proved from the source interior and the actual proper ordered suffix. -/
theorem actual_ordered_loopDeleted_conductance
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (R : EdgeRotation (copyA D P marked) (copyB D P marked))
    (da db : Dart (Copy D P marked))
    (ha : tail (copyA D P marked) (copyB D P marked) da = alpha D P)
    (hb : tail (copyA D P marked) (copyB D P marked) db = beta D P)
    (j0 j1 : Fin (incidenceCount (copyA D P marked) (copyB D P marked) (alpha D P)))
    (hj : j0.val + 1 = j1.val) :
    let J := Canonical.latticeCopiedGraph D P marked
    let hne : alpha D P ≠ beta D P := by intro h; cases h
    let hbeta : beta D P ≠ alpha D P := hne.symm
    let s := orderedSide R (alpha D P) (beta D P) hne da db ha hb j1.val
    let hc := (Repair8.graph_connected D P hD marked).preconnected
    ∃ hK : (supportGraph (groundedSplitGraph J (alpha D P) (beta D P) s).left
        (groundedSplitGraph J (alpha D P) (beta D P) s).right).Preconnected,
      effectiveConductance (loopDeletedSplitGraph J (alpha D P) (beta D P) s)
        (.inr false) (.inr true) (by intro h; cases h) (deleteLoops_preconnected _ hK) =
      effectiveConductance (groundedSplitGraph J (alpha D P) (beta D P) s)
        (.inr false) (.inr true) (by intro h; cases h) hK ∧
      effectiveConductance (loopDeletedSplitGraph J (alpha D P) (beta D P) s)
        (.inr false) (.inr true) (by intro h; cases h) (deleteLoops_preconnected _ hK) =
      responseEntry (splitGraph J (alpha D P) s).left (splitGraph J (alpha D P) s).right
        (splitTerminals (alpha D P) (beta D P) hbeta)
        (split_terminal_reachable J.left J.right (alpha D P) (beta D P) hbeta s hc) 1 1 := by
  intro J hne hbeta s hc
  have hsuffix := (ordered_split_terminals_incident R (alpha D P) (beta D P)
    hne da db ha hb (copy_loopless D P marked) j0 j1 hj).2
  let hK := grounded_preconnected D P marked s hD hsuffix
  refine ⟨hK,deleteLoops_effectiveConductance _ _ _ (by intro h; cases h) hK,?_⟩
  exact loopDeleted_effectiveConductance_eq_total_response J (alpha D P)
    (beta D P) hbeta s hc hK

end
end ElectricalFollowup.LoopDeletion
