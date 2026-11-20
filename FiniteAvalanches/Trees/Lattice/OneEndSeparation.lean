import FiniteAvalanches.Trees.Lattice.DualRayParity
import FiniteAvalanches.Trees.Lattice.Topology

/-! One end of a spanning lattice tree whose dual is connected.

For a present primal edge `e`, the dual path joining the two ends of the dual edge of
`e`, closed by that dual edge, is a closed dual trail. Its ray-crossing parity set is a
finite set of primal sites that `e` leaves and no other present primal edge leaves
(`exists_finite_separation_of_dual_connected`). A simple path between two components of
a finite deletion crosses such an edge once, so in a connected graph whose edges all have
finite separating sets every finite deletion has at most one infinite component
(`componentCompl_eq_of_infinite_of_separation`). This is the planar duality argument of
Benjamini–Lyons–Peres–Schramm (2001), Theorem 12.4, and Lyons–Peres, Theorem 10.36, with
the separation by a dual cycle proved by ray-crossing parity. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice
open LatticeProb
open scoped Classical

noncomputable section

/-- Membership in a set is constant along walks whose steps preserve it. -/
theorem walk_iff_of_adj {W : Type*} {H : SimpleGraph W} (P : W → Prop)
    (hP : ∀ x y, H.Adj x y → (P x ↔ P y)) :
    ∀ {x y : W} (_ : H.Walk x y), P x ↔ P y
  | _, _, .nil => Iff.rfl
  | _, _, .cons h p => (hP _ _ h).trans (walk_iff_of_adj P hP p)

/-- If only the edge `s(a, b)` changes membership in `S`, and it does, then a walk
changes membership exactly when it uses that edge an odd number of times. -/
theorem walk_mem_iff_even_count {V : Type*} {G : SimpleGraph V} (S : Set V) {a b : V}
    (hab : a ∈ S ↔ b ∉ S)
    (hS : ∀ x y, G.Adj x y → s(x, y) ≠ s(a, b) → (x ∈ S ↔ y ∈ S)) :
    ∀ {x y : V} (p : G.Walk x y), ((x ∈ S ↔ y ∈ S) ↔ Even (p.edges.count s(a, b)))
  | _, _, .nil => by simp
  | x, _, .cons (v := x') h p => by
    have ih := walk_mem_iff_even_count S hab hS p
    rw [SimpleGraph.Walk.edges_cons, List.count_cons]
    by_cases he : s(x, x') = s(a, b)
    · have hx : x ∈ S ↔ x' ∉ S := by
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hab
        · tauto
      rw [if_pos (by simpa using he), Nat.even_add_one, ← ih]
      tauto
    · rw [if_neg (by simpa using he), add_zero, ← ih]
      have := hS x x' h he
      tauto

/-- Membership in a set that no edge inside `Kᶜ` changes is constant on each
component of the complement of `K`. -/
theorem componentCompl_mem_iff {V : Type*} {G : SimpleGraph V} {K : Set V} (S : Set V)
    (hS : ∀ x y, x ∉ K → y ∉ K → G.Adj x y → (x ∈ S ↔ y ∈ S))
    (C : G.ComponentCompl K) {v w : V} (hv : v ∈ C) (hw : w ∈ C) : v ∈ S ↔ w ∈ S := by
  obtain ⟨hvK, hvC⟩ := hv
  obtain ⟨hwK, hwC⟩ := hw
  have hreach : (G.induce Kᶜ).Reachable ⟨v, hvK⟩ ⟨w, hwK⟩ :=
    SimpleGraph.ConnectedComponent.exact (hvC.trans hwC.symm)
  obtain ⟨p⟩ := hreach
  exact walk_iff_of_adj (fun u : (Kᶜ : Set V) => (u : V) ∈ S)
    (fun x y hxy => hS x y x.property y.property hxy) p

/-- In a preconnected graph in which every edge leaves some finite set that no other
edge leaves, every finite deletion has at most one infinite component. -/
theorem componentCompl_eq_of_infinite_of_separation {V : Type*} {G : SimpleGraph V}
    (hG : G.Preconnected)
    (hsep : ∀ a b, G.Adj a b → ∃ S : Set V, S.Finite ∧ (a ∈ S ↔ b ∉ S) ∧
      ∀ x y, G.Adj x y → s(x, y) ≠ s(a, b) → (x ∈ S ↔ y ∈ S))
    (K : Set V) (C D : G.ComponentCompl K) (hC : C.supp.Infinite) (hD : D.supp.Infinite) :
    C = D := by
  by_contra hne
  obtain ⟨c, hc⟩ := hC.nonempty
  obtain ⟨d, hd⟩ := hD.nonempty
  have hc' : c ∈ C := hc
  have hd' : d ∈ D := hd
  have hdC : d ∉ (C : Set V) := by
    intro hdC
    apply hne
    obtain ⟨hdK, hdC'⟩ := (hdC : d ∈ C)
    obtain ⟨hdK', hdD'⟩ := hd'
    exact hdC'.symm.trans hdD'
  set q := (hG c d).some.bypass with hq
  have hqpath : q.IsPath := (hG c d).some.bypass_isPath
  obtain ⟨dt, hdt, ha, hb⟩ := q.exists_boundary_dart (C : Set V) hc' hdC
  have hbK : dt.snd ∈ K := by
    by_contra hbK
    exact hb (SimpleGraph.ComponentCompl.mem_of_adj dt.fst dt.snd ha hbK dt.adj)
  obtain ⟨S, hSfin, hab, hS⟩ := hsep dt.fst dt.snd dt.adj
  have hinside : ∀ x y, x ∉ K → y ∉ K → G.Adj x y → (x ∈ S ↔ y ∈ S) := by
    intro x y hx hy hxy
    refine hS x y hxy fun he => ?_
    rcases Sym2.eq_iff.mp he with ⟨-, h⟩ | ⟨h, -⟩
    · exact hy (h ▸ hbK)
    · exact hx (h ▸ hbK)
  have hcount : q.edges.count s(dt.fst, dt.snd) = 1 := by
    refine List.count_eq_one_of_mem hqpath.isTrail.edges_nodup ?_
    have : dt.edge ∈ q.edges := List.mem_map_of_mem hdt
    simpa [SimpleGraph.Dart.edge] using this
  have hpar := walk_mem_iff_even_count S hab hS q
  rw [hcount] at hpar
  obtain ⟨c₁, hc₁, hc₁S⟩ := (hC.sdiff hSfin).nonempty
  obtain ⟨d₁, hd₁, hd₁S⟩ := (hD.sdiff hSfin).nonempty
  have hcS : c ∉ S := fun h =>
    hc₁S ((componentCompl_mem_iff S hinside C hc' hc₁).mp h)
  have hdS : d ∉ S := fun h =>
    hd₁S ((componentCompl_mem_iff S hinside D hd' hd₁).mp h)
  exact (by decide : ¬ Even 1) (hpar.mp ⟨fun h => absurd h hcS, fun h => absurd h hdS⟩)

/-- Every lattice edge in Sym2 form is based at one of its ends. -/
theorem exists_base_of_mem_edgeSet {d : Sym2 (Site 2)} (hd : d ∈ (lattice 2).edgeSet) :
    ∃ z : Site 2, ∃ i : Fin 2, d = s(z, z + unit i) := by
  induction d using Sym2.ind with
  | _ x y =>
    obtain ⟨i, h | h⟩ := hd
    · change y = x + unit i at h
      exact ⟨x, i, by rw [h]⟩
    · change x = y + unit i at h
      exact ⟨y, i, by rw [h, Sym2.eq_swap]⟩

/-- A present primal edge of a field with connected dual leaves a finite set of sites
that no other present primal edge leaves. -/
theorem exists_finite_separation_of_dual_connected (ω : EdgeField)
    (hD : (toGraph (dualField ω)).Connected) {a b : Site 2} (hab : (toGraph ω).Adj a b) :
    ∃ S : Set (Site 2), S.Finite ∧ (a ∈ S ↔ b ∉ S) ∧
      ∀ x y, (toGraph ω).Adj x y → s(x, y) ≠ s(a, b) → (x ∈ S ↔ y ∈ S) := by
  obtain ⟨hlat, hω⟩ := hab
  set e : LatticeEdge := ⟨s(a, b), hlat⟩ with he
  obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep (dualEdgeOf e).val
  have huv' : (dualEdgeOf e).val = s(u, v) := huv.symm
  have hadj : (lattice 2).Adj u v := by
    have := (dualEdgeOf e).property
    rw [huv'] at this
    exact this
  have hdual_false : dualField ω (dualEdgeOf e) = false := by
    rw [dualField_dualEdgeOf, hω]
    rfl
  set P := ((hD.preconnected v u).some.bypass).mapLe (toGraph_le_lattice (dualField ω)) with hP
  have hPpath : P.IsPath :=
    (SimpleGraph.Walk.isPath_mapLe _).mpr (hD.preconnected v u).some.bypass_isPath
  have hPedges : ∀ d ∈ P.edges, ∃ hd : d ∈ (lattice 2).edgeSet,
      dualField ω ⟨d, hd⟩ = true := by
    intro d hdP
    rw [hP, SimpleGraph.Walk.edges_mapLe_eq_edges] at hdP
    have hdG := SimpleGraph.Walk.edges_subset_edgeSet _ hdP
    rw [toGraph_edgeSet] at hdG
    exact hdG
  have hnot : s(u, v) ∉ P.edges := by
    intro hmem
    obtain ⟨hd, htrue⟩ := hPedges _ hmem
    have hEq : (⟨s(u, v), hd⟩ : LatticeEdge) = dualEdgeOf e := Subtype.ext huv'.symm
    rw [hEq, hdual_false] at htrue
    exact Bool.false_ne_true htrue
  set c : (lattice 2).Walk u u := SimpleGraph.Walk.cons hadj P with hc
  have hctrail : c.IsTrail :=
    (SimpleGraph.Walk.isTrail_cons hadj P).mpr ⟨hPpath.isTrail, hnot⟩
  set D : Finset (Sym2 (Site 2)) := hctrail.edgesFinset with hDdef
  have hmemD : ∀ d, d ∈ D ↔ d = s(u, v) ∨ d ∈ P.edges := by
    intro d
    change d ∈ c.edges ↔ _
    rw [hc, SimpleGraph.Walk.edges_cons, List.mem_cons]
  have hlatD : ∀ d ∈ D, ∃ z : Site 2, ∃ i : Fin 2, d = s(z, z + unit i) := by
    intro d hd
    exact exists_base_of_mem_edgeSet (c.edges_subset_edgeSet hd)
  have hevenD : ∀ w : Site 2, ∑ d ∈ D, (if w ∈ d then 1 else 0 : ZMod 2) = 0 := by
    intro w
    rw [Finset.sum_boole, ZMod.natCast_eq_zero_iff_even]
    have hev := (hctrail.even_countP_edges_iff w).mpr (fun h => absurd rfl h)
    have hcard : (D.filter (fun d => w ∈ d)).card = c.edges.countP (fun d => w ∈ d) := by
      rw [List.countP_eq_length_filter]
      rfl
    simpa [hcard] using hev
  refine ⟨{x | rayParity D x = 1}, ?_, ?_, ?_⟩
  · refine (rayParity_support_finite D hlatD hevenD).subset fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [hx]
    decide
  · have h := rayParity_add_of_adj D hlatD hevenD hlat
    have hin : (dualEdgeOf ⟨s(a, b), hlat⟩).val ∈ D := (hmemD _).mpr (Or.inl huv')
    rw [if_pos hin] at h
    simp only [Set.mem_setOf_eq]
    generalize rayParity D a = p at h ⊢
    generalize rayParity D b = p' at h ⊢
    revert p p'
    decide
  · rintro x y ⟨hxy, hωxy⟩ hne
    have h := rayParity_add_of_adj D hlatD hevenD hxy
    have hout : (dualEdgeOf ⟨s(x, y), hxy⟩).val ∉ D := by
      rw [hmemD]
      rintro (h1 | h1)
      · have : dualEdgeOf ⟨s(x, y), hxy⟩ = dualEdgeOf e := Subtype.ext (h1.trans huv'.symm)
        exact hne (congrArg Subtype.val (dualEdgeOf_injective this))
      · obtain ⟨hd, htrue⟩ := hPedges _ h1
        have hdf := dualField_dualEdgeOf ω ⟨s(x, y), hxy⟩
        rw [hωxy] at hdf
        have : (⟨(dualEdgeOf ⟨s(x, y), hxy⟩).val, hd⟩ : LatticeEdge) =
            dualEdgeOf ⟨s(x, y), hxy⟩ := rfl
        rw [this, hdf] at htrue
        exact Bool.false_ne_true htrue
    rw [if_neg hout] at h
    simp only [Set.mem_setOf_eq]
    generalize rayParity D x = p at h ⊢
    generalize rayParity D y = p' at h ⊢
    revert p p'
    decide

/-- A spanning lattice tree whose dual field is connected has exactly one infinite
component after every finite deletion. -/
theorem existsUnique_infinite_componentCompl_of_dual_connected (ω : EdgeField)
    (hT : IsTree ω) (hD : (toGraph (dualField ω)).Connected) (K : Finset (Site 2)) :
    ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite := by
  haveI : Fact (toGraph ω).Preconnected := ⟨hT.connected.preconnected⟩
  obtain ⟨en, hen⟩ := SimpleGraph.nonempty_ends_of_infinite (toGraph ω)
  refine ⟨en (Opposite.op K),
    SimpleGraph.end_componentCompl_infinite (toGraph ω) ⟨en, hen⟩ (Opposite.op K), ?_⟩
  intro C hC
  exact componentCompl_eq_of_infinite_of_separation hT.connected.preconnected
    (fun _ _ h => exists_finite_separation_of_dual_connected ω hD h) _ C _ hC
    (SimpleGraph.end_componentCompl_infinite (toGraph ω) ⟨en, hen⟩ (Opposite.op K))

end

end FiniteAvalanches.Trees.Lattice
