import FiniteAvalanches.Trees.Lattice.DualWalkSeparation
import FiniteAvalanches.Trees.RootedPaths

/-! Pasts in a wired spanning tree of a finite volume `Γ`.

A tree `T` with a root `s` (the wired sink) is linked to a lattice edge field `ω` on `Γ`
when the sites of `Γ` are the vertices other than the root, adjacency between them is
adjacency in `ω`, and only sites with a lattice neighbour outside `Γ` are adjacent to the
root. The past of `B` is the set of sites whose path to the root meets `B`. Its local
event `pastEvent` holds, and a site of `B` whose present edges are dual-certified inside a
box has its past inside that box. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice

open LatticeProb FiniteAvalanches.Trees.RootedPaths
open scoped Classical

noncomputable section

section WiredTree

variable {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) (s : V) (ι : Site 2 → V)

/-- The tree is the wired tree of the volume `Γ` with lattice edge field `ω`. -/
structure WiredTreeLink (Γ : Finset (Site 2)) (ω : EdgeField) : Prop where
  inj : ∀ x ∈ Γ, ∀ y ∈ Γ, ι x = ι y → x = y
  ne_root : ∀ x ∈ Γ, ι x ≠ s
  cover : ∀ v, v = s ∨ ∃ x ∈ Γ, v = ι x
  adj : ∀ x ∈ Γ, ∀ y ∈ Γ, (T.Adj (ι x) (ι y) ↔ (toGraph ω).Adj x y)
  field : ∀ x y, (toGraph ω).Adj x y → x ∈ Γ ∧ y ∈ Γ
  exit : ∀ x ∈ Γ, T.Adj (ι x) s → ∃ z, (lattice 2).Adj x z ∧ z ∉ Γ

/-- The site `x` lies in the past of `B`: its path to the root meets `B`. -/
def InPast (B : Finset (Site 2)) (x : Site 2) : Prop :=
  ∃ b ∈ B, ι b ∈ (path hT s (ι x)).support

theorem not_inPast_iff (B : Finset (Site 2)) (x : Site 2) :
    ¬InPast hT s ι B x ↔ ∃ p : T.Walk (ι x) s, ∀ b ∈ B, ι b ∉ p.support := by
  constructor
  · intro h
    refine ⟨(path hT s (ι x)).reverse, fun b hb hmem => h ⟨b, hb, ?_⟩⟩
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hmem
    exact hmem
  · rintro ⟨p, hp⟩ ⟨b, hb, hmem⟩
    have heq : path hT s (ι x) = p.bypass.reverse :=
      path_eq hT _ p.bypass_isPath.reverse
    rw [heq, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hmem
    exact hp b hb (p.support_bypass_subset_support hmem)

variable {hT s ι}

theorem inPast_of_mem {B : Finset (Site 2)} {b : Site 2} (hb : b ∈ B) : InPast hT s ι B b :=
  ⟨b, hb, (path hT s (ι b)).end_mem_support⟩

/-- Sites joined to the root avoiding `B` reach the inner boundary of `W ⊆ Γ`
avoiding `B`. -/
theorem linked_boundary_of_walk {Γ : Finset (Site 2)} {ω : EdgeField}
    (hL : WiredTreeLink (T := T) s ι Γ ω) {B W : Finset (Site 2)} (hWΓ : W ⊆ Γ) :
    ∀ {v w : V} (p : T.Walk v w), w = s → (∀ b ∈ B, ι b ∉ p.support) → ∀ z ∈ W, v = ι z →
      ∃ u ∈ innerBoundary W, Linked ω ((W : Set (Site 2)) \ (B : Set (Site 2))) z u := by
  intro v w p
  induction p with
  | nil =>
    intro hw _ z hz hv
    exact absurd (hv.symm.trans hw) (hL.ne_root z (hWΓ hz))
  | @cons a c _ hac q ih =>
    intro hw hB z hz ha
    subst ha
    have hzB : z ∉ B := fun hzB => hB z hzB (List.mem_cons_self)
    rcases hL.cover c with rfl | ⟨y, hy, rfl⟩
    · obtain ⟨w, hw, hwΓ⟩ := hL.exit z (hWΓ hz) hac
      exact ⟨z, ⟨hz, w, hw, fun hwW => hwΓ (hWΓ hwW)⟩, Relation.ReflTransGen.refl⟩
    · have hzy := (hL.adj z (hWΓ hz) y hy).mp hac
      by_cases hyW : y ∈ W
      · have hB' : ∀ b ∈ B, ι b ∉ q.support := fun b hb hm =>
          hB b hb (List.mem_cons_of_mem _ hm)
        obtain ⟨u, hu, hyu⟩ := ih hw hB' y hyW rfl
        have hyB : y ∉ B := fun hyB => hB' y hyB q.start_mem_support
        exact ⟨u, hu, Relation.ReflTransGen.head ⟨⟨hz, hzB⟩, ⟨hyW, hyB⟩, hzy⟩ hyu⟩
      · exact ⟨z, ⟨hz, y, toGraph_le_lattice ω hzy, hyW⟩, Relation.ReflTransGen.refl⟩

/-- The past of `B` in a wired tree satisfies its local event. -/
theorem pastEvent_of_inPast {Γ : Finset (Site 2)} {ω : EdgeField}
    (hL : WiredTreeLink (T := T) s ι Γ ω) {B S W : Finset (Site 2)} (hBΓ : B ⊆ Γ)
    (hWΓ : W ⊆ Γ) (hnbr : ∀ b ∈ B, ∀ w, (lattice 2).Adj b w → w ∈ W)
    (hS : ∀ x, x ∈ S ↔ x ∈ Γ ∧ InPast hT s ι B x) : ω ∈ pastEvent B S W := by
  refine ⟨fun b hb => (hS b).mpr ⟨hBΓ hb, inPast_of_mem hb⟩, ?_, ?_⟩
  · intro x hx hxB y hxy
    obtain ⟨hxΓ, hyΓ⟩ := hL.field x y hxy
    refine (hS y).mpr ⟨hyΓ, ?_⟩
    by_contra hy
    obtain ⟨p, hp⟩ := (not_inPast_iff hT s ι B y).mp hy
    have hxB' : ∀ b ∈ B, ι b ≠ ι x := fun b hb he =>
      hxB ((hL.inj b (hBΓ hb) x hxΓ he) ▸ hb)
    have hadj := (hL.adj x hxΓ y hyΓ).mpr hxy
    apply ((not_inPast_iff hT s ι B x).mpr ⟨SimpleGraph.Walk.cons hadj p, fun b hb hm => ?_⟩)
      ((hS x).mp hx).2
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
    rcases hm with hm | hm
    · exact hxB' b hb hm
    · exact hp b hb hm
  · intro b hb w hw hbw
    have hwΓ := (hL.field b w hbw).2
    have hwpast : ¬InPast hT s ι B w := fun h => hw ((hS w).mpr ⟨hwΓ, h⟩)
    obtain ⟨p, hp⟩ := (not_inPast_iff hT s ι B w).mp hwpast
    exact linked_boundary_of_walk hL hWΓ p rfl hp w (hnbr b hb w (toGraph_le_lattice ω hbw)) rfl

/-- A site of a dual-certified past lies in the certifying box. -/
theorem inPast_bounded {Γ : Finset (Site 2)} {ω : EdgeField}
    (hL : WiredTreeLink (T := T) s ι Γ ω) {b : Site 2} (hbΓ : b ∈ Γ)
    (hnb : ∀ z, (lattice 2).Adj b z → z ∈ Γ) {k : ℕ}
    (hbox : ∀ x : Site 2, |x 0| ≤ k → |x 1| ≤ k → ∀ z, (lattice 2).Adj x z → z ∈ Γ)
    (hcert : ω ∉ tightEvent b (centeredBox k)) {x : Site 2} (hx : x ∈ Γ)
    (hpast : ι b ∈ (path hT s (ι x)).support) : |x 0| ≤ k ∧ |x 1| ≤ k := by
  have hne : ι b ≠ s := hL.ne_root b hbΓ
  obtain ⟨w, hadj, q', hq⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne (path hT (ι b) s)
  rcases hL.cover w with rfl | ⟨c, hc, rfl⟩
  · obtain ⟨z, hz, hzΓ⟩ := hL.exit b hbΓ hadj
    exact absurd (hnb z hz) hzΓ
  have hbc : (toGraph ω).Adj b c := (hL.adj b hbΓ c hc).mp hadj
  have hcertified : DualCertified ω (centeredBox k : Set (Site 2)) ⟨s(b, c), hbc.1⟩ := by
    by_contra hno
    exact hcert ⟨⟨s(b, c), hbc.1⟩, Sym2.mem_mk_left _ _, hbc.2, hno⟩
  obtain ⟨u, v, huv, hlink⟩ := hcertified
  have huv_ne : u ≠ v := by
    intro he
    have := (dualEdgeOf ⟨s(b, c), hbc.1⟩).property
    rw [huv, he] at this
    exact (lattice 2).loopless.irrefl v this
  have hu : u ∈ centeredBox k := by
    rcases Relation.ReflTransGen.cases_head hlink with he | ⟨_, hstep, _⟩
    · exact absurd he huv_ne
    · exact hstep.1
  obtain ⟨P, hP⟩ := exists_walk_of_dualLinked hlink
  have hPbound : ∀ z ∈ P.reverse.support, |z 0| ≤ (k : ℤ) ∧ |z 1| ≤ (k : ℤ) := by
    intro z hz
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    have hzb : z ∈ centeredBox k := by
      rcases hP z hz with rfl | hz'
      · exact hu
      · exact hz'
    rw [mem_centeredBox] at hzb
    exact ⟨abs_le.mpr (hzb 0), abs_le.mpr (hzb 1)⟩
  obtain ⟨S, hSbox, hSbc, hSsep⟩ :=
    exists_box_separation_of_dual_walk ω hbc huv P.reverse k hPbound
  let S' : Set V := {v | ∃ y ∈ Γ, y ∈ S ∧ v = ι y}
  have hmemS' : ∀ y ∈ Γ, (ι y ∈ S' ↔ y ∈ S) := by
    intro y hy
    constructor
    · rintro ⟨y', hy', hyS, he⟩
      rw [hL.inj y hy y' hy' he]
      exact hyS
    · intro hyS
      exact ⟨y, hy, hyS, rfl⟩
  have hsS' : s ∉ S' := by
    rintro ⟨y, hy, -, he⟩
    exact hL.ne_root y hy he.symm
  have hout : ∀ y ∈ Γ, T.Adj (ι y) s → y ∉ S := by
    intro y hy hys hyS
    obtain ⟨z, hz, hzΓ⟩ := hL.exit y hy hys
    obtain ⟨h0, h1⟩ := hSbox y hyS
    exact hzΓ (hbox y h0 h1 z hz)
  have hab : ι b ∈ S' ↔ ι c ∉ S' := by
    rw [hmemS' b hbΓ, hmemS' c hc]
    exact hSbc
  have hsep : ∀ v w, T.Adj v w → s(v, w) ≠ s(ι b, ι c) → (v ∈ S' ↔ w ∈ S') := by
    intro v w hvw hne'
    rcases hL.cover v with rfl | ⟨y, hy, rfl⟩ <;> rcases hL.cover w with rfl | ⟨z, hz, rfl⟩
    · exact absurd hvw (T.loopless.irrefl _)
    · rw [hmemS' z hz]
      exact ⟨fun h => absurd h hsS', fun h => absurd h (hout z hz hvw.symm)⟩
    · rw [hmemS' y hy]
      exact ⟨fun h => absurd h (hout y hy hvw), fun h => absurd h hsS'⟩
    · rw [hmemS' y hy, hmemS' z hz]
      refine hSsep y z ((hL.adj y hy z hz).mp hvw) fun he => hne' ?_
      rw [show s(ι y, ι z) = Sym2.map ι s(y, z) from rfl, he]
      rfl
  have hcount : (path hT s (ι x)).edges.count s(ι b, ι c) = 1 := by
    refine List.count_eq_one_of_mem (path_isPath hT s (ι x)).isTrail.edges_nodup ?_
    rw [path_split hT hpast, SimpleGraph.Walk.edges_append, List.mem_append]
    left
    rw [path_reverse hT s (ι b), hq, SimpleGraph.Walk.edges_reverse, List.mem_reverse,
      SimpleGraph.Walk.edges_cons]
    exact List.mem_cons_self
  have hpar := walk_mem_iff_even_count S' hab hsep (path hT s (ι x))
  rw [hcount] at hpar
  have hxS' : ι x ∈ S' := by
    by_contra hxS'
    exact (by decide : ¬Even 1) (hpar.mp ⟨fun h => absurd h hsS', fun h => absurd h hxS'⟩)
  exact hSbox x ((hmemS' x hx).mp hxS')

end WiredTree

end

end FiniteAvalanches.Trees.Lattice
