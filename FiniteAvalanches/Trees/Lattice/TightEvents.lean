import FiniteAvalanches.Trees.Lattice.PastEventsInfinite

/-! Dual certificates for pasts. A present edge whose dual edge has its two ends joined by
present dual edges inside `W` encloses the past behind it (ray-crossing parity). The
event `tightEvent b W` that some present edge at `b` has no such certificate inside `W`
depends on finitely many edges and decreases to the empty set when the dual field is
connected. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice

open LatticeProb Filter
open scoped Classical

noncomputable section

/-- Connection by present dual edges through dual sites of `W`. -/
def DualLinked (ω : EdgeField) (W : Set (Site 2)) : Site 2 → Site 2 → Prop :=
  Relation.ReflTransGen fun y z => y ∈ W ∧ z ∈ W ∧ (toGraph (dualField ω)).Adj y z

/-- The ends of the dual edge of `e` are joined by present dual edges inside `W`. -/
def DualCertified (ω : EdgeField) (W : Set (Site 2)) (e : LatticeEdge) : Prop :=
  ∃ u v : Site 2, (dualEdgeOf e).val = s(u, v) ∧ DualLinked ω W u v

/-- Some present edge at `b` has no dual certificate inside `W`. -/
def tightEvent (b : Site 2) (W : Finset (Site 2)) : Set EdgeField :=
  {ω | ∃ e : LatticeEdge, b ∈ e.val ∧ ω e = true ∧ ¬DualCertified ω (W : Set (Site 2)) e}

theorem dualLinked_mono {ω : EdgeField} {W W' : Set (Site 2)} (h : W ⊆ W') {u v : Site 2}
    (huv : DualLinked ω W u v) : DualLinked ω W' u v :=
  Relation.ReflTransGen.mono (fun _ _ hab => ⟨h hab.1, h hab.2.1, hab.2.2⟩) u v huv

theorem tightEvent_anti (b : Site 2) {W W' : Finset (Site 2)} (h : W ⊆ W') :
    tightEvent b W' ⊆ tightEvent b W := by
  rintro ω ⟨e, hbe, hωe, hno⟩
  refine ⟨e, hbe, hωe, fun ⟨u, v, he, huv⟩ => hno ⟨u, v, he, dualLinked_mono ?_ huv⟩⟩
  exact Finset.coe_subset.mpr h

theorem mem_edgesAt_singleton {b : Site 2} (e : LatticeEdge) (hb : b ∈ e.val) :
    e ∈ edgesAt {b} := by
  rcases e with ⟨e, he⟩
  revert he hb
  refine Sym2.ind (fun x y => ?_) e
  intro he hb
  rcases Sym2.mem_iff.mp hb with rfl | rfl
  · exact mem_edgesAt he (Or.inl (Finset.mem_singleton_self _))
  · exact mem_edgesAt he (Or.inr (Finset.mem_singleton_self _))

/-- The primal edge crossed by a dual edge. -/
def primalOf (d : LatticeEdge) : LatticeEdge := edgeEquiv (dualBase (edgeEquiv.symm d))

theorem dualField_apply (ω : EdgeField) (d : LatticeEdge) : dualField ω d = !ω (primalOf d) := rfl

theorem isClopen_tightEvent (b : Site 2) (W : Finset (Site 2)) :
    IsClopen (tightEvent b W) := by
  apply isClopen_of_determined (edgesAt {b} ∪ (edgesAt W).image primalOf)
  have hdual : ∀ ω ω' : EdgeField,
      (∀ e ∈ edgesAt {b} ∪ (edgesAt W).image primalOf, ω e = ω' e) →
      ∀ y z, y ∈ (W : Set (Site 2)) → (toGraph (dualField ω)).Adj y z →
        (toGraph (dualField ω')).Adj y z := by
    intro ω ω' hE y z hy ⟨h, hd⟩
    refine ⟨h, ?_⟩
    rw [dualField_apply] at hd ⊢
    rw [← hE _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (mem_edgesAt h (Or.inl hy))))]
    exact hd
  have key : ∀ ω ω' : EdgeField,
      (∀ e ∈ edgesAt {b} ∪ (edgesAt W).image primalOf, ω e = ω' e) →
      ω ∈ tightEvent b W → ω' ∈ tightEvent b W := by
    intro ω ω' hE ⟨e, hbe, hωe, hno⟩
    have heE : e ∈ edgesAt {b} := mem_edgesAt_singleton e hbe
    refine ⟨e, hbe, (hE e (Finset.mem_union_left _ heE)) ▸ hωe, fun ⟨u, v, he, huv⟩ => hno ⟨u, v,
      he, ?_⟩⟩
    have hE' : ∀ e ∈ edgesAt {b} ∪ (edgesAt W).image primalOf, ω' e = ω e :=
      fun e he => (hE e he).symm
    exact Relation.ReflTransGen.mono (fun y z hyz =>
      ⟨hyz.1, hyz.2.1, hdual ω' ω hE' y z hyz.1 hyz.2.2⟩) u v huv
  intro ω ω' hE
  exact ⟨key ω ω' hE, key ω' ω fun e he => (hE e he).symm⟩

/-- With a connected dual field, every edge is eventually certified inside large boxes. -/
theorem eventually_dualCertified (ω : EdgeField) (hD : (toGraph (dualField ω)).Connected)
    (e : LatticeEdge) : ∀ᶠ m in atTop, DualCertified ω (centeredBox m : Set (Site 2)) e := by
  obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep (dualEdgeOf e).val
  obtain ⟨p⟩ := hD.preconnected u v
  filter_upwards [eventually_subset_centeredBox p.support.toFinset] with m hm
  refine ⟨u, v, huv.symm, ?_⟩
  have key : ∀ {a c : Site 2} (q : (toGraph (dualField ω)).Walk a c),
      (∀ z ∈ q.support, z ∈ centeredBox m) → DualLinked ω (centeredBox m : Set (Site 2)) a c := by
    intro a c q
    induction q with
    | nil => intro _; exact Relation.ReflTransGen.refl
    | cons h q ih =>
      intro hs
      refine Relation.ReflTransGen.head ⟨hs _ (List.mem_cons_self), hs _
        (List.mem_cons_of_mem _ q.start_mem_support), h⟩ (ih fun z hz => hs z
          (List.mem_cons_of_mem _ hz))
  exact key p fun z hz => hm (List.mem_toFinset.mpr hz)

/-- With a connected dual field, the tightness events at `b` are eventually empty. -/
theorem eventually_not_mem_tightEvent (ω : EdgeField) (hD : (toGraph (dualField ω)).Connected)
    (b : Site 2) : ∀ᶠ m in atTop, ω ∉ tightEvent b (centeredBox m) := by
  have hall : ∀ᶠ m in atTop, ∀ e ∈ edgesAt {b}, DualCertified ω (centeredBox m : Set (Site 2)) e :=
    (edgesAt {b}).eventually_all.mpr fun e _ => eventually_dualCertified ω hD e
  filter_upwards [hall] with m hm
  rintro ⟨e, hbe, -, hno⟩
  exact hno (hm e (mem_edgesAt_singleton e hbe))

end

end FiniteAvalanches.Trees.Lattice
