import FiniteAvalanches.Trees.RootedPaths

set_option autoImplicit false
namespace FiniteAvalanches.Trees.FiniteCirculation
open SimpleGraph
open scoped Classical BigOperators
noncomputable section
variable {V : Type*}

/-- Finite antisymmetric currents have zero total flux across every vertex cut
when their divergence vanishes. The vertex window contains the current support. -/
theorem cut_flux_zero (W : Finset V) (f : V → V → ℤ)
    (hanti : ∀ x y, f x y = -f y x)
    (hdiv : ∀ x ∈ W, ∑ y ∈ W, f x y = 0) (C : Set V) :
    ∑ x ∈ W.filter (· ∈ C), ∑ y ∈ W.filter (· ∉ C), f x y = 0 := by
  let S := W.filter (· ∈ C)
  let R := W.filter (· ∉ C)
  have hinternal : ∑ x ∈ S, ∑ y ∈ S, f x y = 0 := by
    have hneg : (∑ x ∈ S, ∑ y ∈ S, f x y) = -(∑ x ∈ S, ∑ y ∈ S, f x y) := by
      calc
        (∑ x ∈ S, ∑ y ∈ S, f x y) = ∑ y ∈ S, ∑ x ∈ S, f x y := Finset.sum_comm
        _ = -(∑ x ∈ S, ∑ y ∈ S, f x y) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro y _
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro x _
          exact hanti x y
    omega
  have hsum : ∑ x ∈ S, ∑ y ∈ W, f x y = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact hdiv x (Finset.mem_filter.mp hx).1
  have hsplit : ∀ x, (∑ y ∈ W, f x y) = (∑ y ∈ S, f x y) + ∑ y ∈ R, f x y := by
    intro x
    exact (Finset.sum_filter_add_sum_filter_not W (· ∈ C) (f x)).symm
  simp_rw [hsplit] at hsum
  rw [Finset.sum_add_distrib, hinternal, zero_add] at hsum
  exact hsum

/-- A divergence-free finite current cannot have exactly one nonzero coefficient
crossing a cut. All hypotheses concern the literal finite current and vertex cut. -/
theorem zero_of_unique_cut_crossing (W : Finset V) (f : V → V → ℤ)
    (hanti : ∀ x y, f x y = -f y x)
    (hdiv : ∀ x ∈ W, ∑ y ∈ W, f x y = 0) (C : Set V)
    (x y : V) (hxW : x ∈ W) (hyW : y ∈ W) (hxC : x ∈ C) (hyC : y ∉ C)
    (hsole : ∀ u ∈ C, ∀ z ∉ C, f u z ≠ 0 → u = x ∧ z = y) : f x y = 0 := by
  have hflux := cut_flux_zero W f hanti hdiv C
  have hxS : x ∈ W.filter (· ∈ C) := Finset.mem_filter.mpr ⟨hxW, hxC⟩
  have hyR : y ∈ W.filter (· ∉ C) := Finset.mem_filter.mpr ⟨hyW, hyC⟩
  have heval : (∑ u ∈ W.filter (· ∈ C), ∑ z ∈ W.filter (· ∉ C), f u z) = f x y := by
    rw [Finset.sum_eq_single_of_mem x hxS]
    · apply Finset.sum_eq_single_of_mem y hyR
      intro z hz hzy
      by_contra hf
      exact hzy (hsole x hxC z (Finset.mem_filter.mp hz).2 hf).2
    · intro u hu hux
      apply Finset.sum_eq_zero
      intro z hz
      by_contra hf
      exact hux (hsole u (Finset.mem_filter.mp hu).2 z (Finset.mem_filter.mp hz).2 hf).1
  exact heval.symm.trans hflux

/-- A finite-support circulation on a genuine tree plus one exceptional edge is
supported on the unique tree path between that edge's endpoints and the edge itself.
No cycle or relationship between a supplied boundary and a path is assumed. -/
theorem support_mem_path_or_exception (T : SimpleGraph V) (hT : T.IsTree)
    (a b : V) (W : Finset V) (f : V → V → ℤ)
    (hanti : ∀ x y, f x y = -f y x)
    (hfinite : ∀ x y, f x y ≠ 0 → x ∈ W ∧ y ∈ W)
    (hdiv : ∀ x ∈ W, ∑ y ∈ W, f x y = 0)
    (hsupport : ∀ x y, f x y ≠ 0 → T.Adj x y ∨ s(x, y) = s(a, b))
    (x y : V) (hxy : f x y ≠ 0) :
    s(x, y) ∈ (RootedPaths.path hT a b).edges ∨ s(x, y) = s(a, b) := by
  by_contra hn
  push Not at hn
  obtain ⟨hnotpath, hnotexception⟩ := hn
  have hadj : T.Adj x y := (hsupport x y hxy).resolve_right hnotexception
  let D := T.deleteEdges {s(x, y)}
  let C : Set V := {z | D.Reachable x z}
  have hxC : x ∈ C := Reachable.refl x
  have hyC : y ∉ C :=
    (isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) hadj))
  have hab : D.Reachable a b :=
    reachable_deleteEdges_iff_exists_walk.mpr ⟨RootedPaths.path hT a b, hnotpath⟩
  have hsole : ∀ u ∈ C, ∀ z ∉ C, f u z ≠ 0 → u = x ∧ z = y := by
    intro u hu z hz hf
    rcases hsupport u z hf with ht | he
    · by_cases he : s(u, z) = s(x, y)
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · exact False.elim (hyC hu)
      · have hd : D.Adj u z := deleteEdges_adj.mpr ⟨ht, by simpa only [Set.mem_singleton_iff]⟩
        exact False.elim (hz (hu.trans hd.reachable))
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim (hz (hu.trans hab))
      · exact False.elim (hz (hu.trans hab.symm))
  obtain ⟨hxW, hyW⟩ := hfinite x y hxy
  exact hxy (zero_of_unique_cut_crossing W f hanti hdiv C x y hxW hyW hxC hyC hsole)

end
end FiniteAvalanches.Trees.FiniteCirculation
