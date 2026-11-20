import FiniteAvalanches.Trees.Lattice.OneEndSeparation

/-! Local events describing the union of the pasts of a finite set `B` of sites.

`pastEvent B S V` says that no present edge leaves `S` except at `B`, and that every
neighbour of `B` outside `S` joined to `B` by a present edge is joined to the inner
boundary of `V` by present edges avoiding `B`. It depends on finitely many edges, and it
is decreasing in `V` once `V` contains the neighbours of `B`. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice

open LatticeProb
open scoped Classical

noncomputable section

/-- The sites of `V` with a lattice neighbour outside `V`. -/
def innerBoundary (V : Finset (Site 2)) : Set (Site 2) :=
  {u | u ∈ V ∧ ∃ y, (lattice 2).Adj u y ∧ y ∉ V}

/-- Connection by present edges through sites of `W`. -/
def Linked (ω : EdgeField) (W : Set (Site 2)) : Site 2 → Site 2 → Prop :=
  Relation.ReflTransGen fun x y => x ∈ W ∧ y ∈ W ∧ (toGraph ω).Adj x y

/-- The local event that the union of the pasts of `B` is `S`, seen inside `V`. -/
def pastEvent (B S V : Finset (Site 2)) : Set EdgeField :=
  {ω | B ⊆ S ∧ (∀ x ∈ S, x ∉ B → ∀ y, (toGraph ω).Adj x y → y ∈ S) ∧
    ∀ b ∈ B, ∀ w, w ∉ S → (toGraph ω).Adj b w →
      ∃ u ∈ innerBoundary V, Linked ω ((V : Set (Site 2)) \ (B : Set (Site 2))) w u}

theorem linked_mono {ω : EdgeField} {W W' : Set (Site 2)} (h : W ⊆ W') {x y : Site 2}
    (hxy : Linked ω W x y) : Linked ω W' x y :=
  Relation.ReflTransGen.mono (fun _ _ hab => ⟨h hab.1, h hab.2.1, hab.2.2⟩) x y hxy

/-- A connection to the inner boundary of a larger set first reaches the inner boundary of
a smaller one. -/
theorem linked_exit {ω : EdgeField} {B V V' : Finset (Site 2)} (hVV' : V ⊆ V') {w u : Site 2}
    (h : Linked ω ((V' : Set (Site 2)) \ (B : Set (Site 2))) w u) (hu : u ∈ innerBoundary V')
    (hw : w ∈ V) :
    ∃ u' ∈ innerBoundary V, Linked ω ((V : Set (Site 2)) \ (B : Set (Site 2))) w u' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨-, y, hy, hyV'⟩ := hu
    exact ⟨_, ⟨hw, y, hy, fun hyV => hyV' (hVV' hyV)⟩, Relation.ReflTransGen.refl⟩
  | @head a c hstep _ ih =>
    obtain ⟨ha, hc, hac⟩ := hstep
    by_cases hcV : c ∈ V
    · obtain ⟨u', hu', hcu'⟩ := ih hcV
      refine ⟨u', hu', Relation.ReflTransGen.head ⟨⟨hw, ha.2⟩, ⟨hcV, hc.2⟩, hac⟩ hcu'⟩
    · exact ⟨a, ⟨hw, c, toGraph_le_lattice ω hac, hcV⟩, Relation.ReflTransGen.refl⟩

/-- The past event is decreasing in `V` once `V` contains the neighbours of `B`. -/
theorem pastEvent_anti {B S V V' : Finset (Site 2)} (hVV' : V ⊆ V')
    (hnbr : ∀ b ∈ B, ∀ w, (lattice 2).Adj b w → w ∈ V) :
    pastEvent B S V' ⊆ pastEvent B S V := by
  rintro ω ⟨hBS, h1, h2⟩
  refine ⟨hBS, h1, fun b hb w hw hbw => ?_⟩
  obtain ⟨u, hu, hwu⟩ := h2 b hb w hw hbw
  exact linked_exit hVV' hwu hu (hnbr b hb w (toGraph_le_lattice ω hbw))

/-- The lattice edges with an endpoint in a finite set of sites. -/
def edgesAt (T : Finset (Site 2)) : Finset LatticeEdge :=
  ((T ∪ T.image (· - unit 0) ∪ T.image (· - unit 1)) ×ˢ (Finset.univ : Finset (Fin 2))).image
    baseEdge

theorem mem_edgesAt {T : Finset (Site 2)} {x y : Site 2} (h : (lattice 2).Adj x y)
    (hx : x ∈ T ∨ y ∈ T) : (⟨s(x, y), h⟩ : LatticeEdge) ∈ edgesAt T := by
  have key : ∀ (z : Site 2) (i : Fin 2), (z ∈ T ∨ z + unit i ∈ T) →
      baseEdge (z, i) ∈ edgesAt T := by
    intro z i hz
    apply Finset.mem_image.mpr
    refine ⟨(z, i), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
    rcases hz with hz | hz
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
    · fin_cases i
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨_, hz, by simp⟩))
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hz, by simp⟩)
  obtain ⟨i, hy | hx'⟩ := id h
  · change y = x + unit i at hy
    subst hy
    have := key x i (hx.imp id id)
    exact this
  · change x = y + unit i at hx'
    subst hx'
    have he : (⟨s(y + unit i, y), h⟩ : LatticeEdge) = baseEdge (y, i) :=
      Subtype.ext Sym2.eq_swap
    rw [he]
    exact key y i hx.symm

/-- A set of edge fields determined by finitely many coordinates is clopen. -/
theorem isClopen_of_determined (E : Finset LatticeEdge) (A : Set EdgeField)
    (h : ∀ ω ω' : EdgeField, (∀ e ∈ E, ω e = ω' e) → (ω ∈ A ↔ ω' ∈ A)) : IsClopen A := by
  have hA : A = E.restrict ⁻¹' (E.restrict '' A) := by
    ext ω
    constructor
    · intro hω
      exact ⟨ω, hω, rfl⟩
    · rintro ⟨ω', hω', he⟩
      exact (h ω' ω fun e he' => congrFun he ⟨e, he'⟩).mp hω'
  rw [hA]
  have hc : Continuous (E.restrict : EdgeField → E → Bool) :=
    continuous_pi fun e => continuous_apply e.val
  exact (isClopen_discrete _).preimage hc

theorem toGraph_adj_congr {ω ω' : EdgeField} {x y : Site 2} (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ω e = ω' e) (hxy : ∀ h : (lattice 2).Adj x y, (⟨s(x, y), h⟩ : LatticeEdge) ∈ E) :
    (toGraph ω).Adj x y ↔ (toGraph ω').Adj x y := by
  constructor
  · rintro ⟨h, hω⟩
    exact ⟨h, (hE _ (hxy h)) ▸ hω⟩
  · rintro ⟨h, hω⟩
    exact ⟨h, (hE _ (hxy h)).symm ▸ hω⟩

theorem linked_congr {ω ω' : EdgeField} {W : Set (Site 2)} (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ω e = ω' e)
    (hW : ∀ x y, x ∈ W → (lattice 2).Adj x y → ∀ h : (lattice 2).Adj x y,
      (⟨s(x, y), h⟩ : LatticeEdge) ∈ E) {x y : Site 2} (hxy : Linked ω W x y) :
    Linked ω' W x y :=
  Relation.ReflTransGen.mono (fun a b hab =>
    ⟨hab.1, hab.2.1, (toGraph_adj_congr E hE
      (hW a b hab.1 (toGraph_le_lattice ω hab.2.2))).mp hab.2.2⟩) x y hxy

theorem isClopen_pastEvent (B S V : Finset (Site 2)) : IsClopen (pastEvent B S V) := by
  apply isClopen_of_determined (edgesAt (S ∪ V))
  have key : ∀ ω ω' : EdgeField, (∀ e ∈ edgesAt (S ∪ V), ω e = ω' e) →
      ω ∈ pastEvent B S V → ω' ∈ pastEvent B S V := by
    intro ω ω' hE ⟨hBS, h1, h2⟩
    have hS : ∀ x y, x ∈ S → ∀ h : (lattice 2).Adj x y,
        (⟨s(x, y), h⟩ : LatticeEdge) ∈ edgesAt (S ∪ V) :=
      fun x y hx h => mem_edgesAt h (Or.inl (Finset.mem_union_left _ hx))
    refine ⟨hBS, fun x hx hxB y hxy => h1 x hx hxB y ?_, fun b hb w hw hbw => ?_⟩
    · exact (toGraph_adj_congr _ hE (hS x y hx)).mpr hxy
    · obtain ⟨u, hu, hwu⟩ := h2 b hb w hw
        ((toGraph_adj_congr _ hE (hS b w (hBS hb))).mpr hbw)
      refine ⟨u, hu, linked_congr _ hE (fun x y hx _ h => ?_) hwu⟩
      exact mem_edgesAt h (Or.inl (Finset.mem_union_right _ hx.1))
  intro ω ω' hE
  exact ⟨key ω ω' hE, key ω' ω fun e he => (hE e he).symm⟩

end

end FiniteAvalanches.Trees.Lattice
