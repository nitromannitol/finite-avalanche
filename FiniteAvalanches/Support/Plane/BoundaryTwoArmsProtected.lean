import FiniteAvalanches.Support.Plane.BoundarySecondArm

/-!
# Two boundary arms with reserved stubs

Two prescribed accesses can be joined to a common root while preserving an
arbitrary finite supply of separated stubs and avoiding all other accesses.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Two boundary accesses admit separated arms with prescribed terminal speed
and any requested number of protected root stubs. -/
theorem exists_two_boundary_arms_with_protected_stubs
    {ι : Type*} [DecidableEq ι] {U S : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (a : ∀ i, Path (x i) (y i))
    (ha : ∀ i ∈ s, Function.Injective (a i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (a i) ∩ U) (range (a j)))
    (haU : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → a i t ∈ U)
    (hy : ∀ i ∈ s, y i ∉ U) (hS : S.Finite)
    (haS : ∀ i ∈ s, Disjoint (range (a i)) S)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) (n : ℕ) :
    ∃ (r : ℝ × ℝ) (q : Fin n → ℝ × ℝ)
      (p : ∀ l, Path (q l) r) (v : Path r (y i)) (w : Path r (y j)),
      r ∈ (U \ ⋃ l ∈ s, range (a l)) \ S ∧
      Function.Injective v ∧ Function.Injective w ∧
      range v ⊆ (U ∪ {y i}) \ S ∧ range w ⊆ (U ∪ {y j}) \ S ∧
      (∀ l, q l ≠ r ∧ Function.Injective (p l) ∧
        range (p l) ⊆ (U \ ⋃ k ∈ s, range (a k)) \ S ∧
        range (p l) ∩ range v = {r} ∧ range (p l) ∩ range w = {r}) ∧
      (∀ l m, l ≠ m → range (p l) ∩ range (p m) = {r}) ∧
      (∀ z ∈ range w ∩ range v, z = r ∨ z = y j ∧ y j = y i) ∧
      Disjoint (range v ∩ U) (⋃ l ∈ s.erase i, range (a l)) ∧
      Disjoint (range w ∩ U) (⋃ l ∈ (s.erase i).erase j, range (a l)) ∧
      (∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          v t = a i ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) ∧
      (∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w t = a j ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) := by
  classical
  obtain ⟨r, q, p, v, hr, hv, hvU, hp, hpair, havoid, htail, hc⟩ :=
    exists_first_boundary_arm_with_connected_complement hU hconn hUne s a ha hd haU hy hS haS hi (n + 1)
  have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  obtain ⟨w, hw, hwU, hwv, hprotect, hwavoid, hwtail⟩ :=
    exists_second_boundary_arm_with_protected_stubs hU hS s a ha hd haU hy haS
      p v (fun z hz => (hvU hz).1) hp hpair havoid hc hj' (Fin.last n)
  let q' : Fin n → ℝ × ℝ := fun l => q l.castSucc
  let p' : ∀ l, Path (q' l) r := fun l => p l.castSucc
  have hne : ∀ l : Fin n, l.castSucc ≠ Fin.last n := by
    intro l h
    have hh := congrArg Fin.val h
    exact (Nat.ne_of_lt l.isLt) hh
  refine ⟨r, q', p', v, w, hr, hv, hw, hvU, hwU, ?_, ?_, hwv,
    havoid, hwavoid, htail, hwtail⟩
  · intro l
    exact ⟨(hp l.castSucc).1, (hp l.castSucc).2.1, (hp l.castSucc).2.2.1,
      (hp l.castSucc).2.2.2, hprotect l.castSucc (hne l)⟩
  · intro l m hlm
    exact hpair l.castSucc m.castSucc (fun h => hlm (Fin.castSucc_injective n h))

end FiniteAvalanches.Electrical.StatementGeometry
