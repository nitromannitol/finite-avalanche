import FiniteAvalanches.Support.Plane.BoundaryProtectedFamily

/-!
# Protected attachment of boundary accesses

A boundary access can be joined to a rooted tree while protecting finitely
many root stubs and avoiding the other accesses in the region.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A boundary access can be attached with its terminal speed preserved while
protecting a finite family of root stubs and avoiding the other accesses. -/
theorem exists_boundary_path_with_protected_stubs_avoiding_accesses
    {ι κ : Type*} [DecidableEq ι] {U K S : Set (ℝ × ℝ)} {r q : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hK : IsFiniteArcTree r K)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (a : ∀ i, Path (x i) (y i))
    (ha : ∀ i ∈ s, Function.Injective (a i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (a i) ∩ U) (range (a j)))
    (haU : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → a i t ∈ U)
    (hy : ∀ i ∈ s, y i ∉ U) (hS : S.Finite)
    (haS : ∀ i ∈ s, Disjoint (range (a i)) S)
    (hKU : K ⊆ U \ ⋃ i ∈ s, range (a i))
    (t : Finset κ) {z : κ → ℝ × ℝ} (p : ∀ j, Path (z j) r)
    (hp : ∀ j ∈ t, Function.Injective (p j))
    (hpU : ∀ j ∈ t, range (p j) ⊆ (U \ ⋃ i ∈ s, range (a i)) \ S)
    (hpK : ∀ j ∈ t, range (p j) ∩ K = {r})
    (hpp : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → range (p j) ∩ range (p k) = {r})
    (v : Path q r) (hv : Function.Injective v)
    (hvU : range v ⊆ (U \ ⋃ i ∈ s, range (a i)) \ S)
    (hvK : range v ∩ K = {r})
    (hvp : ∀ j ∈ t, range v ∩ range (p j) = {r})
    (hq : q ∉ K ∪ ⋃ j ∈ t, range (p j)) {i : ι} (hi : i ∈ s) :
    ∃ w : Path r (y i), Function.Injective w ∧ range w ⊆ (U ∪ {y i}) \ S ∧
      IsFiniteArcTree r (range w ∪ K) ∧
      (∀ j ∈ t, range (p j) ∩ (range w ∪ K) = {r}) ∧
      Disjoint (range w ∩ U) (⋃ j ∈ s.erase i, range (a j)) ∧
      ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (v : unitInterval) (hv : ((u : ℝ) + 1) / 2 ≤ (v : ℝ)),
          w v = a i ⟨2 * (v : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [v.property.2]⟩ := by
  let A := ⋃ j ∈ s.erase i, range (a j)
  let W := U \ A
  have hAclosed : IsClosed A :=
    ((s.erase i).isCompact_biUnion (fun j _ => isCompact_range (a j).continuous)).isClosed
  have hW : IsOpen W := hU.sdiff hAclosed
  have hWconn : IsPreconnected W := by
    apply isPreconnected_sdiff_finset_paths_of_disjoint_inside hU hconn (s.erase i) a
    · intro j hj
      exact ha j (Finset.mem_of_mem_erase hj)
    · intro j hj k hk hjk
      exact hd j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk) hjk
    · intro j hj
      exact isPreconnected_range_inter_compl_of_mem_except_target (a j)
        (haU j (Finset.mem_of_mem_erase hj)) (hy j (Finset.mem_of_mem_erase hj))
  have hA : A ⊆ ⋃ j ∈ s, range (a j) := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_of_mem_erase hj, hzj⟩
  have hKUW : K ⊆ W := fun z hz => ⟨(hKU hz).1, fun h => (hKU hz).2 (hA h)⟩
  have hpUW : ∀ j ∈ t, range (p j) ⊆ W \ S := by
    intro j hj z hz
    have hh := hpU j hj hz
    exact ⟨⟨hh.1.1, fun h => hh.1.2 (hA h)⟩, hh.2⟩
  have hvUW : range v ⊆ W \ S := by
    intro z hz
    have hh := hvU hz
    exact ⟨⟨hh.1.1, fun h => hh.1.2 (hA h)⟩, hh.2⟩
  have haW : ∀ u : unitInterval, u ≠ 1 → a i u ∈ W := by
    intro u hu
    refine ⟨haU i hi u hu, ?_⟩
    intro hz
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hz
    exact disjoint_left.mp (hd i hi j (Finset.mem_of_mem_erase hj)
      (Ne.symm (Finset.ne_of_mem_erase hj))) ⟨⟨u, rfl⟩, haU i hi u hu⟩ hzj
  have hyW : y i ∉ W := fun h => hy i hi h.1
  have haK : Disjoint (range (a i)) ((K ∪ ⋃ j ∈ t, range (p j)) ∪ range v) := by
    apply disjoint_left.mpr
    intro z hz hzK
    have hza : z ∈ ⋃ j ∈ s, range (a j) := mem_iUnion₂.mpr ⟨i, hi, hz⟩
    rcases hzK with (hzK | hzP) | hzv
    · exact (hKU hzK).2 hza
    · obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzP
      exact (hpU j hj hzj).1.2 hza
    · exact (hvU hzv).1.2 hza
  obtain ⟨w, hw, hwW, htree, hprotected, u, hu, htail⟩ :=
    exists_boundary_path_to_root_with_protected_family hW hWconn hK hKUW hS t p hp hpUW
      hpK hpp v hv hvUW hvK hvp hq (a i) (ha i hi) haW hyW (haS i hi) haK
  refine ⟨w, hw, ?_, htree, hprotected, ?_, u, hu, htail⟩
  · intro z hz
    rcases hwW hz with ⟨hzW | hzy, hzS⟩
    · exact ⟨Or.inl hzW.1, hzS⟩
    · exact ⟨Or.inr hzy, hzS⟩
  · apply disjoint_left.mpr
    intro z ⟨hzw, hzU⟩ hzA
    rcases hwW hzw with ⟨hzW | hzy, _⟩
    · exact hzW.2 hzA
    · exact hy i hi ((mem_singleton_iff.mp hzy) ▸ hzU)

end FiniteAvalanches.Electrical.StatementGeometry
