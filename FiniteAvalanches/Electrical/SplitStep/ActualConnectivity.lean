import FiniteAvalanches.Electrical.SplitStep.ActualEnergy
import FiniteAvalanches.Electrical.ChordSplit.LoopDeletedResponse

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.ChordSplit
open FiniteAvalanches.Electrical.Source
open scoped Classical
noncomputable section

theorem grounded_terminals_ne (D : Finset (Site 2)) (P : OneSet D) :
    (Sum.inr false : GroundedSplitVertex (alpha D P) (beta D P)) ≠ Sum.inr true :=
  Sum.inr_injective.ne (by decide)

def interiorVertex (D : Finset (Site 2)) (P : OneSet D) (x : D) :
    SplitVertex (alpha D P) :=
  .inl ⟨project D P x.val, fun h => ((project_eq_alpha_iff D P _).mp h) x.property⟩

theorem internal_split_copy_reachable (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ)
    (e : OriginalCopy) (ha : originalA e ∈ D) (hb : originalB e ∈ D) :
    (supportGraph (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right).Reachable
      (interiorVertex D P ⟨originalA e, ha⟩) (interiorVertex D P ⟨originalB e, hb⟩) := by
  by_cases heq : project D P (originalA e) = project D P (originalB e)
  · have h : interiorVertex D P ⟨originalA e, ha⟩ = interiorVertex D P ⟨originalB e, hb⟩ :=
      congrArg Sum.inl (Subtype.ext heq)
    rw [h]
  · let c : Copy D P marked := ⟨e, (mem_retainedCopies D P marked e).mpr
      ⟨Or.inl ha, heq, Repair8.internal_ne_marked D P marked e ha hb⟩⟩
    apply SimpleGraph.Adj.reachable
    refine ⟨?_, c, Or.inl ⟨?_, ?_⟩⟩
    · intro h
      exact heq (congrArg (collapse (alpha D P)) h)
    · exact (splitEndpoint_eq_inl _ _ _ _ _).mpr rfl
    · exact (splitEndpoint_eq_inl _ _ _ _ _).mpr rfl

theorem internal_split_adj_reachable (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ)
    (x y : D) (hxy : (lattice 2).Adj x.val y.val) :
    (supportGraph (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right).Reachable
      (interiorVertex D P x) (interiorVertex D P y) := by
  change ∃ j : Fin 2, y.val = x.val + unit j ∨ x.val = y.val + unit j at hxy
  obtain ⟨j, h | h⟩ := hxy
  · have hy : originalB (x.val, j) ∈ D := by change x.val + unit j ∈ D; rw [← h]; exact y.property
    have hr := internal_split_copy_reachable D P marked copies i (x.val, j) x.property hy
    exact hr.trans (by
      have hv : interiorVertex D P ⟨originalB (x.val, j), hy⟩ = interiorVertex D P y :=
        congrArg (interiorVertex D P) (Subtype.ext h.symm)
      rw [hv])
  · have hx : originalB (y.val, j) ∈ D := by change y.val + unit j ∈ D; rw [← h]; exact x.property
    have hr := (internal_split_copy_reachable D P marked copies i (y.val, j) y.property hx).symm
    have hv : interiorVertex D P ⟨originalB (y.val, j), hx⟩ = interiorVertex D P x :=
      congrArg (interiorVertex D P) (Subtype.ext h.symm)
    rw [hv] at hr
    exact hr

/-- Every original interior path lifts without visiting either split alpha terminal. -/
theorem internal_split_reachable (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ)
    (x y : D) :
    (supportGraph (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right).Reachable
      (interiorVertex D P x) (interiorVertex D P y) := by
  have hr := (SimpleGraph.reachable_iff_reflTransGen x y).mp (hD x y)
  induction hr with
  | refl => exact .rfl
  | @tail u v _ huv ih =>
    exact ih.trans (internal_split_adj_reachable D P marked copies i u v huv)

theorem internal_split_reaches_beta (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) (x : D) :
    (supportGraph (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right).Reachable (interiorVertex D P x)
      (.inl ⟨beta D P, by intro h; cases h⟩) := by
  obtain ⟨p, hp⟩ := P.property
  have hb : project D P p.val = beta D P := (project_eq_beta_iff D P _).mpr
    (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have hv : interiorVertex D P p = .inl ⟨beta D P, by intro h; cases h⟩ :=
    congrArg Sum.inl (Subtype.ext hb)
  rw [← hv]
  exact internal_split_reachable D P hD marked copies i x p

theorem nonalpha_split_reaches_beta (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ)
    (v : {x : Vertex D P // x ≠ alpha D P}) :
    (supportGraph (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right).Reachable (.inl v)
      (.inl ⟨beta D P, by intro h; cases h⟩) := by
  rcases v with ⟨v, hv⟩
  cases v with
  | inl k =>
    cases k
    · exact (hv rfl).elim
    · exact .rfl
  | inr x =>
    have he : interiorVertex D P x.val = .inl ⟨Sum.inr x, hv⟩ :=
      congrArg Sum.inl (Subtype.ext (project_free D P x))
    rw [← he]
    exact internal_split_reaches_beta D P hD marked copies i x.val

theorem boundary_split_reaches_beta (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ)
    (k : Fin m) :
    (supportGraph (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right).Reachable (.inr (decide (i ≤ k.val)))
      (.inl ⟨beta D P, by intro h; cases h⟩) := by
  let e := (copies k).val
  have hs := boundarySide_copy (copyA D P marked) (copyB D P marked) (alpha D P) copies i k
  have hedge : (supportGraph (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right).Reachable
      ((actualSplit D P marked copies i).left e) ((actualSplit D P marked copies i).right e) :=
    SimpleGraph.Adj.reachable ⟨split_endpoint_ne _ _ _ _ (copy_loopless D P marked) e,
      e, Or.inl ⟨rfl, rfl⟩⟩
  rcases (copies k).property with ha | hb
  · have hn : copyB D P marked e ≠ alpha D P := fun h =>
      copy_loopless D P marked e (ha.trans h.symm)
    have hleft : (actualSplit D P marked copies i).left e = .inr (decide (i ≤ k.val)) := by
      change splitEndpoint (alpha D P) (boundarySide _ _ _ copies i)
        (copyA D P marked (copies k).val) (copies k).val = _
      rw [splitEndpoint, dif_pos ha, hs]
    have hright : (actualSplit D P marked copies i).right e = .inl ⟨copyB D P marked e, hn⟩ :=
      (splitEndpoint_eq_inl _ _ _ _ _).mpr rfl
    rw [hleft, hright] at hedge
    exact hedge.trans (nonalpha_split_reaches_beta D P hD marked copies i _)
  · have hn : copyA D P marked e ≠ alpha D P := fun h =>
      copy_loopless D P marked e (h.trans hb.symm)
    have hright : (actualSplit D P marked copies i).right e = .inr (decide (i ≤ k.val)) := by
      change splitEndpoint (alpha D P) (boundarySide _ _ _ copies i)
        (copyB D P marked (copies k).val) (copies k).val = _
      rw [splitEndpoint, dif_pos hb, hs]
    have hleft : (actualSplit D P marked copies i).left e = .inl ⟨copyA D P marked e, hn⟩ :=
      (splitEndpoint_eq_inl _ _ _ _ _).mpr rfl
    rw [hleft, hright] at hedge
    exact hedge.symm.trans (nonalpha_split_reaches_beta D P hD marked copies i _)

/-- For a strict interior split both alpha copies attach to the original connected interior. -/
theorem actual_split_connected (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (i : ℕ) (hi0 : 0 < i) (him : i < m) :
    (supportGraph (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right).Connected := by
  letI : Nonempty (SplitVertex (alpha D P)) := ⟨.inr false⟩
  have reaches (x : SplitVertex (alpha D P)) :
      (supportGraph (actualSplit D P marked copies i).left
        (actualSplit D P marked copies i).right).Reachable x
        (.inl ⟨beta D P, by intro h; cases h⟩) := by
    cases x with
    | inl v => exact nonalpha_split_reaches_beta D P hD marked copies i v
    | inr k =>
      cases k
      · have h := boundary_split_reaches_beta D P hD marked copies i ⟨0, by omega⟩
        simpa only [decide_eq_false (not_le_of_gt hi0)] using h
      · have h := boundary_split_reaches_beta D P hD marked copies i ⟨i, him⟩
        simpa only [decide_eq_true (le_refl i)] using h
  exact ⟨fun x y => (reaches x).trans (reaches y).symm⟩

/-- Identifying alpha0 with beta preserves actual copied connectivity, including loops. -/
theorem actual_grounded_preconnected (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (i : ℕ) (hi0 : 0 < i) (him : i < m) :
    (supportGraph
      (groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
        (boundarySide _ _ _ copies i)).left
      (groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
        (boundarySide _ _ _ copies i)).right).Preconnected := by
  have hsurj : Function.Surjective (groundMap (alpha D P) (beta D P)) := by
    intro x
    cases x with
    | inl v =>
      refine ⟨.inl ⟨v.val, v.property.1⟩, ?_⟩
      simp only [groundMap, dif_neg v.property.2]
    | inr k => exact ⟨.inr k, rfl⟩
  intro x y
  obtain ⟨u, rfl⟩ := hsurj x
  obtain ⟨v, rfl⟩ := hsurj y
  exact mapped_copies_reachable _ _ (groundMap (alpha D P) (beta D P))
    ((actual_split_connected D P hD marked copies i hi0 him).preconnected u v)

/-- Ordinary two-terminal conductance is exactly total R11 on the actual ordered split. -/
theorem actual_conductance_eq_totalResponse (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (i : ℕ) (hi0 : 0 < i) (him : i < m) :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    effectiveConductance K (.inr false) (.inr true) (grounded_terminals_ne D P)
      (actual_grounded_preconnected D P hD marked copies i hi0 him) =
        totalResponse D P hD marked copies i := by
  intro K
  have hK := actual_grounded_preconnected D P hD marked copies i hi0 him
  have hc := (Repair8.graph_connected D P hD marked).preconnected
  exact (deleteLoops_effectiveConductance K (.inr false) (.inr true)
    (grounded_terminals_ne D P) hK).symm.trans
    (loopDeleted_effectiveConductance_eq_total_response (originalGraph D P marked)
      (alpha D P) (beta D P) (by intro h; cases h) _ hc hK)

end
end FiniteAvalanches.Electrical.SplitStep
