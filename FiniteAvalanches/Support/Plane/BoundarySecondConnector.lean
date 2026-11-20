import FiniteAvalanches.Support.Plane.BoundaryFirstComplement
import FiniteAvalanches.Support.Plane.ArcEndpointConnector

/-!
# Connecting a reserved stub to an unused access

After a first boundary arm is chosen, any reserved root stub can be joined to
any remaining access while avoiding the first arm and all other obstacles.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A reserved stub and an unused boundary access admit a simple connector
that avoids the first arm, the other stubs, the other accesses, and a finite set. -/
theorem exists_connector_of_first_boundary_arm
    {ι : Type*} [DecidableEq ι] {U S : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hS : S.Finite) (s : Finset ι)
    {x y : ι → ℝ × ℝ} (a : ∀ i, Path (x i) (y i))
    (ha : ∀ i ∈ s, Function.Injective (a i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (a i) ∩ U) (range (a j)))
    (haU : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → a i t ∈ U)
    (haS : ∀ i ∈ s, Disjoint (range (a i)) S)
    {i : ι} {r : ℝ × ℝ} {n : ℕ} {q : Fin n → ℝ × ℝ}
    (p : ∀ k, Path (q k) r) (w : Path r (y i))
    (hp : ∀ k, q k ≠ r ∧ Function.Injective (p k) ∧
      range (p k) ⊆ (U \ ⋃ l ∈ s, range (a l)) \ S ∧
      range (p k) ∩ range w = {r})
    (hpair : ∀ k l, k ≠ l → range (p k) ∩ range (p l) = {r})
    (havoid : Disjoint (range w ∩ U) (⋃ j ∈ s.erase i, range (a j)))
    (hconn : IsPreconnected (((U \ range w) \ (⋃ j ∈ s.erase i, range (a j))) \
      (⋃ k, range (p k))))
    {j : ι} (hj : j ∈ s.erase i) (k : Fin n) :
    ∃ v : Path (q k) (x j), Function.Injective v ∧ range v ⊆ U \ S ∧
      range v ∩ range (p k) = {q k} ∧ range v ∩ range (a j) = {x j} ∧
      Disjoint (range v) (range w) ∧
      (∀ l, l ≠ k → Disjoint (range v) (range (p l))) ∧
      Disjoint (range v) (⋃ l ∈ (s.erase i).erase j, range (a l)) := by
  classical
  let I := s.erase i
  let P := ⋃ l ∈ (Finset.univ : Finset (Fin n)).erase k, range (p l)
  let A := ⋃ l ∈ I.erase j, range (a l)
  let K := S ∪ range w ∪ A ∪ P
  have hjS : j ∈ s := (Finset.mem_erase.mp hj).2
  have hpk := (hp k).2.2.1 (p k).source_mem_range
  have hxU : x j ∈ U := by simpa only [Path.source] using haU j hjS 0 (by norm_num)
  have hxS : x j ∉ S := fun h => disjoint_left.mp (haS j hjS) (a j).source_mem_range h
  have hqW : q k ∉ range w := by
    intro h
    have h' : q k ∈ range (p k) ∩ range w := ⟨(p k).source_mem_range, h⟩
    rw [(hp k).2.2.2] at h'
    exact (hp k).1 (mem_singleton_iff.mp h')
  have hqP : q k ∉ P := by
    intro h
    obtain ⟨l, hl, h⟩ := mem_iUnion₂.mp h
    have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
    have h' : q k ∈ range (p k) ∩ range (p l) := ⟨(p k).source_mem_range, h⟩
    rw [hpair k l hlk.symm] at h'
    exact (hp k).1 (mem_singleton_iff.mp h')
  have hqA : q k ∉ A := by
    intro h
    apply hpk.1.2
    obtain ⟨l, hl, h⟩ := mem_iUnion₂.mp h
    exact mem_iUnion₂.mpr ⟨l, (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).2, h⟩
  have hqaj : q k ∉ range (a j) := fun h =>
    hpk.1.2 (mem_iUnion₂.mpr ⟨j, hjS, h⟩)
  have hxW : x j ∉ range w := fun h =>
    disjoint_left.mp havoid ⟨h, hxU⟩ (mem_iUnion₂.mpr ⟨j, hj, (a j).source_mem_range⟩)
  have hxP : x j ∉ P := by
    intro h
    obtain ⟨l, _, h⟩ := mem_iUnion₂.mp h
    have hl := (hp l).2.2.1 h
    exact hl.1.2 (mem_iUnion₂.mpr ⟨j, hjS, (a j).source_mem_range⟩)
  have hxA : x j ∉ A := by
    intro h
    obtain ⟨l, hl, h⟩ := mem_iUnion₂.mp h
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hls : l ∈ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).2
    exact disjoint_left.mp (hd j hjS l hls hlj.symm) ⟨(a j).source_mem_range, hxU⟩ h
  have hxp : x j ∉ range (p k) := by
    intro h
    exact ((hp k).2.2.1 h).1.2 (mem_iUnion₂.mpr ⟨j, hjS, (a j).source_mem_range⟩)
  have hK : IsClosed K := by
    apply IsClosed.union
    · apply IsClosed.union
      · exact hS.isClosed.union (isCompact_range w.continuous).isClosed
      · exact ((I.erase j).isCompact_biUnion (fun l _ => isCompact_range (a l).continuous)).isClosed
    · exact (((Finset.univ : Finset (Fin n)).erase k).isCompact_biUnion
        (fun l _ => isCompact_range (p l).continuous)).isClosed
  let Z := ((U \ range w) \ (⋃ l ∈ I, range (a l))) \ (⋃ l, range (p l))
  have hZ : IsOpen Z := ((hU.sdiff (isCompact_range w.continuous).isClosed).sdiff
    (I.isCompact_biUnion (fun l _ => isCompact_range (a l).continuous)).isClosed).sdiff
      (isCompact_iUnion (fun l : Fin n => isCompact_range (p l).continuous)).isClosed
  have hconnected := isPreconnected_sdiff_finite hZ hconn hS
  have hset : U \ (K ∪ range (p k) ∪ range (a j)) = Z \ S := by
    ext t
    simp only [Z, K, P, A, mem_sdiff, mem_union, mem_iUnion, Finset.mem_erase,
      Finset.mem_univ, not_exists, not_or]
    constructor
    · rintro ⟨htU, hother⟩
      obtain ⟨hother, htaj⟩ := hother
      obtain ⟨hother, htpk⟩ := hother
      obtain ⟨hother, htp⟩ := hother
      obtain ⟨hother, hta⟩ := hother
      obtain ⟨htS, htw⟩ := hother
      refine ⟨⟨⟨⟨htU, htw⟩, ?_⟩, ?_⟩, htS⟩
      · intro l hl h
        by_cases hlj : l = j
        · subst l
          exact htaj h
        · exact hta l ⟨hlj, hl⟩ h
      · intro l h
        by_cases hlk : l = k
        · subst l
          exact htpk h
        · exact htp l ⟨hlk, trivial⟩ h
    · rintro ⟨⟨⟨⟨htU, htw⟩, hta⟩, htp⟩, htS⟩
      refine ⟨htU, ?_⟩
      refine ⟨?_, hta j hj⟩
      refine ⟨?_, htp k⟩
      exact ⟨⟨⟨htS, htw⟩, fun l hl => hta l hl.2⟩, fun l _ => htp l⟩
  have hc : IsPreconnected (U \ (K ∪ range (p k) ∪ range (a j))) :=
    hset.symm ▸ hconnected
  have hqK : q k ∉ K := by
    simp only [K, mem_union, not_or]
    exact ⟨⟨⟨hpk.2, hqW⟩, hqA⟩, hqP⟩
  have hxK : x j ∉ K := by
    simp only [K, mem_union, not_or]
    exact ⟨⟨⟨hxS, hxW⟩, hxA⟩, hxP⟩
  obtain ⟨v, hv, hvU, hvp, hva⟩ := exists_injective_path_between_arc_endpoints
    hU hK (p k) (a j) (hp k).2.1 (ha j hjS)
    ⟨hpk.1.1, fun h => h.elim hqK hqaj⟩ ⟨hxU, fun h => h.elim hxK hxp⟩ hc
  refine ⟨v, hv, ?_, hvp, hva, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨(hvU ht).1, fun h => (hvU ht).2 (Or.inl (Or.inl (Or.inl h)))⟩
  · exact disjoint_left.mpr (fun t ht hw => (hvU ht).2 (Or.inl (Or.inl (Or.inr hw))))
  · intro l hl
    apply disjoint_left.mpr
    intro t ht hp'
    apply (hvU ht).2
    exact Or.inr (mem_iUnion₂.mpr ⟨l, Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩, hp'⟩)
  · apply disjoint_left.mpr
    intro t ht ha'
    exact (hvU ht).2 (Or.inl (Or.inr ha'))

end FiniteAvalanches.Electrical.StatementGeometry
