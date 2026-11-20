import FiniteAvalanches.Trees.Lattice.PastEvents

/-! The past events in a one-ended spanning tree of `ℤ²`.

For a spanning tree in which every finite deletion has exactly one infinite component,
the union of the pasts of a nonempty finite set `B` is the complement of the infinite
component of the deletion of `B`. It is finite, and the past events of `B` with set `S`
hold for all large boxes exactly when `S` is this complement. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice

open LatticeProb Filter
open scoped Classical

noncomputable section

/-- The sites of the box `[-m, m]²`. -/
def centeredBox (m : ℕ) : Finset (Site 2) := Finset.Icc (fun _ => -(m : ℤ)) (fun _ => (m : ℤ))

theorem mem_centeredBox {m : ℕ} {x : Site 2} : x ∈ centeredBox m ↔ ∀ i, -(m : ℤ) ≤ x i ∧ x i ≤ m := by
  simp only [centeredBox, Finset.mem_Icc, Pi.le_def]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

theorem centeredBox_mono {m n : ℕ} (h : m ≤ n) : centeredBox m ⊆ centeredBox n := by
  intro x hx
  rw [mem_centeredBox] at hx ⊢
  intro i
  have := hx i
  have hmn : (m : ℤ) ≤ n := by exact_mod_cast h
  constructor <;> omega

theorem exists_subset_centeredBox (S : Finset (Site 2)) : ∃ m, S ⊆ centeredBox m := by
  refine ⟨∑ z ∈ S, ((z 0).natAbs + (z 1).natAbs), fun z hz => mem_centeredBox.mpr fun i => ?_⟩
  have hle : (z 0).natAbs + (z 1).natAbs ≤ ∑ w ∈ S, ((w 0).natAbs + (w 1).natAbs) :=
    Finset.single_le_sum (f := fun w : Site 2 => (w 0).natAbs + (w 1).natAbs)
      (fun _ _ => Nat.zero_le _) hz
  have hi : (z i).natAbs ≤ (z 0).natAbs + (z 1).natAbs := by
    fin_cases i <;> simp
  have hc : ((z i).natAbs : ℤ) ≤ ((∑ w ∈ S, ((w 0).natAbs + (w 1).natAbs) : ℕ) : ℤ) := by
    exact_mod_cast hi.trans hle
  rw [Int.natCast_natAbs] at hc
  exact abs_le.mp hc

theorem eventually_subset_centeredBox (S : Finset (Site 2)) : ∀ᶠ m in atTop, S ⊆ centeredBox m := by
  obtain ⟨m, hm⟩ := exists_subset_centeredBox S
  filter_upwards [eventually_ge_atTop m] with n hn
  exact hm.trans (centeredBox_mono hn)

/-- Sites of the inner boundary of a box lie on its border. -/
theorem not_mem_centeredBox_of_innerBoundary {m n : ℕ} (hnm : n < m) {u : Site 2}
    (hu : u ∈ innerBoundary (centeredBox m)) : u ∉ centeredBox n := by
  obtain ⟨hum, y, hy, hyb⟩ := hu
  rw [mem_centeredBox] at hum
  intro hun
  rw [mem_centeredBox] at hun
  apply hyb
  rw [mem_centeredBox]
  have hmn : (n : ℤ) < m := by exact_mod_cast hnm
  obtain ⟨i, rfl | rfl⟩ := hy
  · intro j
    obtain ⟨h1, h2⟩ := hun j
    by_cases hij : j = i
    · subst hij
      simp only [Pi.add_apply, unit, Pi.single_eq_same]
      constructor <;> omega
    · simp only [Pi.add_apply, unit, Pi.single_apply, hij, if_false, add_zero]
      exact hum j
  · intro j
    obtain ⟨h1, h2⟩ := hun j
    have hx := hum j
    by_cases hij : j = i
    · subst hij
      simp only [Pi.add_apply, unit, Pi.single_eq_same] at hx h1 h2 ⊢
      constructor <;> omega
    · simp only [Pi.add_apply, unit, Pi.single_apply, hij, if_false, add_zero] at hx ⊢
      exact hx

/-- Two sites of one component after deleting `K` are linked avoiding `K`. -/
theorem linked_of_mem_componentCompl {ω : EdgeField} {K : Set (Site 2)}
    (C : (toGraph ω).ComponentCompl K) {v w : Site 2} (hv : v ∈ C) (hw : w ∈ C) :
    Linked ω Kᶜ v w := by
  obtain ⟨hvK, hvC⟩ := hv
  obtain ⟨hwK, hwC⟩ := hw
  have hreach : ((toGraph ω).induce Kᶜ).Reachable ⟨v, hvK⟩ ⟨w, hwK⟩ :=
    SimpleGraph.ConnectedComponent.exact (hvC.trans hwC.symm)
  obtain ⟨p⟩ := hreach
  have key : ∀ {a b : (Kᶜ : Set (Site 2))} (_ : ((toGraph ω).induce Kᶜ).Walk a b),
      Linked ω Kᶜ a.val b.val := by
    intro a b q
    induction q with
    | nil => exact Relation.ReflTransGen.refl
    | cons h _ ih => exact Relation.ReflTransGen.head ⟨Subtype.prop _, Subtype.prop _, h⟩ ih
  exact key p

/-- Linked sites avoiding `K` lie in one component after deleting `K`. -/
theorem mem_componentCompl_of_linked {ω : EdgeField} {K : Set (Site 2)} {W : Set (Site 2)}
    (hW : W ⊆ Kᶜ) (C : (toGraph ω).ComponentCompl K) {v w : Site 2} (hv : v ∈ C)
    (h : Linked ω W v w) : w ∈ C := by
  induction h with
  | refl => exact hv
  | tail _ hstep ih =>
    obtain ⟨_, hc, hbc⟩ := hstep
    exact SimpleGraph.ComponentCompl.mem_of_adj _ _ ih (hW hc) hbc

/-- A link leaving `V` first reaches the inner boundary of `V`. -/
theorem linked_exit_out {ω : EdgeField} {W : Set (Site 2)} {V : Finset (Site 2)} {w z : Site 2}
    (h : Linked ω W w z) (hw : w ∈ V) (hz : z ∉ V) :
    ∃ u ∈ innerBoundary V, Linked ω ((V : Set (Site 2)) ∩ W) w u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hw hz
  | @head a c hstep _ ih =>
    obtain ⟨ha, hc, hac⟩ := hstep
    by_cases hcV : c ∈ V
    · obtain ⟨u, hu, hcu⟩ := ih hcV
      exact ⟨u, hu, Relation.ReflTransGen.head ⟨⟨hw, ha⟩, ⟨hcV, hc⟩, hac⟩ hcu⟩
    · exact ⟨a, ⟨hw, c, toGraph_le_lattice ω hac, hcV⟩, Relation.ReflTransGen.refl⟩

section OneEnded

variable (ω : EdgeField) (hT : IsTree ω)
  (hU : ∀ K : Finset (Site 2),
    ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)

/-- The infinite component after deleting `B`. -/
def infComp (B : Finset (Site 2)) : (toGraph ω).ComponentCompl (B : Set (Site 2)) :=
  (hU B).exists.choose

theorem infComp_infinite (B : Finset (Site 2)) : (infComp ω hU B).supp.Infinite :=
  (hU B).exists.choose_spec

theorem eq_infComp {B : Finset (Site 2)} (C : (toGraph ω).ComponentCompl (B : Set (Site 2)))
    (hC : C.supp.Infinite) : C = infComp ω hU B :=
  (hU B).unique hC (infComp_infinite ω hU B)

/-- The union of the pasts of `B`: the complement of the infinite component. -/
def pastSet (B : Finset (Site 2)) : Set (Site 2) := ((infComp ω hU B).supp)ᶜ

theorem subset_pastSet (B : Finset (Site 2)) : (B : Set (Site 2)) ⊆ pastSet ω hU B :=
  fun _ hb hC => SimpleGraph.ComponentCompl.notMem_of_mem hC hb

include hT in
theorem pastSet_finite (B : Finset (Site 2)) : (pastSet ω hU B).Finite := by
  haveI : Fact (toGraph ω).Preconnected := ⟨hT.connected.preconnected⟩
  have hsub : pastSet ω hU B ⊆ (B : Set (Site 2)) ∪
      ⋃ C : {C : (toGraph ω).ComponentCompl (B : Set (Site 2)) // C ≠ infComp ω hU B},
        C.val.supp := by
    intro x hx
    by_cases hxB : x ∈ (B : Set (Site 2))
    · exact Or.inl hxB
    · refine Or.inr (Set.mem_iUnion.mpr ⟨⟨(toGraph ω).componentComplMk hxB, fun he => hx ?_⟩,
        (toGraph ω).componentComplMk_mem hxB⟩)
      rw [← he]
      exact (toGraph ω).componentComplMk_mem hxB
  refine (B.finite_toSet.union (Set.finite_iUnion fun C => ?_)).subset hsub
  by_contra hinf
  exact C.property (eq_infComp ω hU C.val hinf)

theorem pastEvent_constant (B S V : Finset (Site 2)) (hω : ω ∈ pastEvent B S V)
    (C : (toGraph ω).ComponentCompl (B : Set (Site 2))) {v w : Site 2} (hv : v ∈ C)
    (hw : w ∈ C) : v ∈ S ↔ w ∈ S := by
  obtain ⟨-, h1, -⟩ := hω
  have hS : ∀ x y, x ∉ (B : Set (Site 2)) → y ∉ (B : Set (Site 2)) → (toGraph ω).Adj x y →
      ((x ∈ (S : Set (Site 2))) ↔ y ∈ (S : Set (Site 2))) := fun x y hx hy hxy =>
    ⟨fun h => h1 x h hx y hxy, fun h => h1 y h hy x hxy.symm⟩
  exact componentCompl_mem_iff (S : Set (Site 2)) hS C hv hw

include hT in
/-- In a one-ended spanning tree the past events of `B` hold for all large boxes exactly
for the complement of the infinite component. -/
theorem eventually_pastEvent_iff {B : Finset (Site 2)} (hB : B.Nonempty) (S : Finset (Site 2)) :
    (∀ᶠ m in atTop, ω ∈ pastEvent B S (centeredBox m)) ↔
      (S : Set (Site 2)) = pastSet ω hU B := by
  constructor
  · intro h
    obtain ⟨m1, hm1⟩ := eventually_atTop.mp h
    have hP := hm1 m1 le_rfl
    ext x
    constructor
    · intro hxS hxC
      have hsub : (infComp ω hU B).supp ⊆ (S : Set (Site 2)) := fun y hy =>
        (pastEvent_constant ω B S _ hP (infComp ω hU B) hxC hy).mp hxS
      exact infComp_infinite ω hU B (S.finite_toSet.subset hsub)
    · intro hx
      by_contra hxS
      have hxB : x ∉ (B : Set (Site 2)) := fun hb => hxS (hP.1 hb)
      set C := (toGraph ω).componentComplMk hxB with hCdef
      have hxCm : x ∈ C := (toGraph ω).componentComplMk_mem hxB
      have hCne : C ≠ infComp ω hU B := fun he => hx (he ▸ hxCm)
      have hCfin : C.supp.Finite := by
        by_contra hinf
        exact hCne (eq_infComp ω hU C hinf)
      have hCS : ∀ y ∈ C, y ∉ S := fun y hy hyS =>
        hxS ((pastEvent_constant ω B S _ hP C hxCm hy).mpr hyS)
      obtain ⟨⟨w, b⟩, hwC, hbB, hwb⟩ :=
        SimpleGraph.ComponentCompl.exists_adj_boundary_pair hT.connected.preconnected
          (Finset.coe_nonempty.mpr hB) C
      obtain ⟨M, hM⟩ := exists_subset_centeredBox hCfin.toFinset
      have hm := hm1 (max m1 (M + 1)) (le_max_left _ _)
      obtain ⟨u, hu, hwu⟩ := hm.2.2 b hbB w (hCS w hwC) hwb.symm
      have huC : u ∈ C := mem_componentCompl_of_linked (fun _ hz => hz.2) C hwC hwu
      exact not_mem_centeredBox_of_innerBoundary (by omega) hu
        (hM (hCfin.mem_toFinset.mpr huC))
  · intro hS
    have hBS : B ⊆ S := by
      intro b hb
      have : b ∈ (S : Set (Site 2)) := hS ▸ subset_pastSet ω hU B hb
      exact this
    obtain ⟨m0, hm0⟩ := exists_subset_centeredBox (B.biUnion nbrFinset)
    filter_upwards [eventually_ge_atTop m0] with m hm
    refine ⟨hBS, fun x hx hxB y hxy => ?_, fun b hb w hw hbw => ?_⟩
    · by_contra hy
      have hyC : y ∈ infComp ω hU B := by
        by_contra hyC
        apply hy
        have : y ∈ (S : Set (Site 2)) := hS ▸ hyC
        exact this
      have hxC := SimpleGraph.ComponentCompl.mem_of_adj y x hyC hxB hxy.symm
      have : x ∈ (S : Set (Site 2)) := hx
      rw [hS] at this
      exact this hxC
    · have hwC : w ∈ infComp ω hU B := by
        by_contra hwC
        apply hw
        have : w ∈ (S : Set (Site 2)) := hS ▸ hwC
        exact this
      have hwbox : w ∈ centeredBox m := centeredBox_mono hm (hm0 (Finset.mem_biUnion.mpr
        ⟨b, hb, (FiniteAvalanches.Sandpile.FiniteWired.mem_neighbors_iff b w).mpr (toGraph_le_lattice ω hbw)⟩))
      obtain ⟨z, hzC, hzbox⟩ := ((infComp_infinite ω hU B).sdiff
        (centeredBox m).finite_toSet).nonempty
      obtain ⟨u, hu, hwu⟩ := linked_exit_out
        (linked_of_mem_componentCompl (infComp ω hU B) hwC hzC) hwbox hzbox
      refine ⟨u, hu, ?_⟩
      have he : (centeredBox m : Set (Site 2)) ∩ (B : Set (Site 2))ᶜ =
          (centeredBox m : Set (Site 2)) \ (B : Set (Site 2)) := rfl
      rw [← he]
      exact hwu

end OneEnded

end

end FiniteAvalanches.Trees.Lattice
