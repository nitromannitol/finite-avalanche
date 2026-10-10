import FiniteAvalanches.Wilson.Lattice.CofiniteClosedContactConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.JointWitnessBounds
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open scoped Classical
noncomputable section

private def upper (t : ℤ) : Set (Site 2) := {x | t ≤ x 0}
private def point (a b : ℤ) : Site 2 := ![a, b]

private theorem upper_horizontal (t : ℤ) (n : ℕ) :
    ((lattice 2).induce (upper t)).Reachable
      ⟨point t 0, by simp [upper, point]⟩
      ⟨point (t + n) 0, by simp [upper, point]⟩ := by
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero]; exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    change (lattice 2).Adj (point (t + n) 0) (point (t + (n + 1 : ℕ)) 0)
    refine ⟨0, Or.inl ?_⟩
    ext i
    fin_cases i <;> simp [point, unit, add_assoc]

private theorem upper_vertical (t a : ℤ) (ha : t ≤ a) (b : ℤ) :
    ((lattice 2).induce (upper t)).Reachable
      ⟨point a 0, ha⟩ ⟨point a b, ha⟩ := by
  induction b using Int.induction_on with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    change (lattice 2).Adj (point a n) (point a (n + 1))
    refine ⟨1, Or.inl ?_⟩
    ext i
    fin_cases i <;> simp [point, unit]
  | pred n ih =>
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    change (lattice 2).Adj (point a (-↑n)) (point a (-↑n - 1))
    refine ⟨1, Or.inr ?_⟩
    ext i
    fin_cases i <;> simp [point, unit]

private theorem upper_connected (t : ℤ) : ((lattice 2).induce (upper t)).Connected := by
  haveI : Nonempty (upper t) := ⟨⟨point t 0, by simp [upper, point]⟩⟩
  have hbase (x : upper t) : ((lattice 2).induce (upper t)).Reachable
      ⟨point t 0, by simp [upper, point]⟩ x := by
    let n := (x.val 0 - t).toNat
    have hn : t + (n : ℤ) = x.val 0 := by
      dsimp only [n]
      rw [Int.toNat_of_nonneg (by exact sub_nonneg.mpr x.property)]
      omega
    have he : point (t + n) (x.val 1) = x.val := by
      ext i
      fin_cases i <;> simp [point, hn]
    have h := (upper_horizontal t n).trans
      (upper_vertical t (t + n) (by omega) (x.val 1))
    have he' : (⟨point (t + n) (x.val 1), by change t ≤ t + (n : ℤ); omega⟩ : upper t) = x := Subtype.ext he
    rwa [he'] at h
  exact ⟨fun x y => (hbase x).symm.trans (hbase y)⟩

private theorem lower_connected :
    ((lattice 2).induce {x : Site 2 | x 0 ≤ 0}).Connected := by
  let φ : (lattice 2).induce (upper 0) →g
      (lattice 2).induce {x : Site 2 | x 0 ≤ 0} := {
    toFun := fun x => ⟨-x.val, by change -x.val 0 ≤ 0; exact neg_nonpos.mpr (show 0 ≤ x.val 0 from x.property)⟩
    map_rel' := by
      intro x y h
      change (lattice 2).Adj x.val y.val at h
      change (lattice 2).Adj (-x.val) (-y.val)
      obtain ⟨i, hi | hi⟩ := h
      · exact ⟨i, Or.inr (by rw [hi]; abel)⟩
      · exact ⟨i, Or.inl (by rw [hi]; abel)⟩ }
  apply SimpleGraph.Connected.map φ _ (upper_connected 0)
  intro x
  refine ⟨⟨-x.val, by change 0 ≤ -x.val 0; exact neg_nonneg.mpr x.property⟩, ?_⟩
  exact Subtype.ext (neg_neg _)

private def testRoots : RootPair where
  zero := {x | x 0 ≤ 0}
  one := upper 1
  disjoint := Set.disjoint_left.mpr (by intro x hx hy; change x 0 ≤ 0 at hx; change 1 ≤ x 0 at hy; omega)
  zero_nonempty := ⟨0, by simp⟩
  one_nonempty := ⟨point 1 0, by simp [upper, point]⟩

private theorem radius_point (a : ℤ) : siteRadius 0 (point a 0) = a.natAbs := by
  simp [siteRadius, point, show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]

/-- A literal admissible pair of half planes bounds the shared probability witness. -/
theorem epsilon_le_one_of_local (ε : ℝ)
    (hlocal : ∀ (r : ℕ), 10 ^ 30 ≤ r → ∀ (R : RootPair),
      (R.zero ∪ R.one)ᶜ.Finite → 0 ∈ R.zero →
      (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
      ((lattice 2).induce R.zero).Connected →
      (∃ x ∈ R.zero, 2 * r ≤ siteRadius 0 x) →
      ((lattice 2).induce R.one).Connected →
      (∃ y ∈ R.one, siteRadius 0 y = r) →
      ε ≤ (wilsonColorLaw R).real
        (localContactEvent R.zero 0 (2 * r) ((1 / 8 : ℝ) * Real.log (r : ℝ)))) :
    ε ≤ 1 := by
  let r : ℕ := 10 ^ 30
  have hr : 1 ≤ r := by exact Nat.one_le_iff_ne_zero.mpr (by dsimp only [r]; positivity)
  have hfinite : (testRoots.zero ∪ testRoots.one)ᶜ.Finite := by
    have he : testRoots.zero ∪ testRoots.one = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      change x 0 ≤ 0 ∨ 1 ≤ x 0
      omega
    rw [he, Set.compl_univ]
    exact Set.finite_empty
  have hb : ∃ b ∈ testRoots.one, (lattice 2).Adj 0 b := by
    refine ⟨point 1 0, by simp [testRoots, upper, point], 0, Or.inl ?_⟩
    ext i
    fin_cases i <;> simp [point, unit]
  have hx : ∃ x ∈ testRoots.zero, 2 * r ≤ siteRadius 0 x := by
    refine ⟨point (-(2 * (r : ℤ))) 0, ?_, ?_⟩
    · change -(2 * (r : ℤ)) ≤ 0
      omega
    · rw [radius_point, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast]
      norm_num
  have hy : ∃ y ∈ testRoots.one, siteRadius 0 y = r := by
    refine ⟨point r 0, ?_, ?_⟩
    · change 1 ≤ (r : ℤ)
      exact_mod_cast hr
    · rw [radius_point, Int.natAbs_natCast]
  exact (hlocal r le_rfl testRoots hfinite (by simp [testRoots]) hb
    lower_connected hx (upper_connected 1) hy).trans measureReal_le_one

end
end FiniteAvalanches.Wilson.Lattice.JointWitnessBounds
