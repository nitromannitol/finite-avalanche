import FiniteAvalanches.Electrical.Trees.GroveNoncrossing
import Mathlib.Tactic

namespace FiniteAvalanches.Electrical.PairFormula
open FiniteAvalanches.Electrical
instance (a b c d : Fin 6) : Decidable (chords_cross a b c d) :=
  inferInstanceAs (Decidable (_ ∨ _))
instance (U W : Fin 3 → Fin 6) (p : Equiv.Perm (Fin 3)) :
    Decidable (triple_noncrossing U W p) :=
  inferInstanceAs (Decidable (∀ i j, i ≠ j → ¬chords_cross (U i) (W (p i)) (U j) (W (p j))))

/-- The ordered source triples, using zero-based cyclic ranks. -/
def triple124 : Fin 3 → Fin 6 := ![0,1,3]
def triple356 : Fin 3 → Fin 6 := ![2,4,5]
def triple123 : Fin 3 → Fin 6 := ![0,1,2]
def triple456 : Fin 3 → Fin 6 := ![3,4,5]

/-- Pairing 16|23|45 between the triples 124 and 356. -/
def matching162345 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 0 2
/-- Pairing 16|25|34, between either pair of source triples. -/
def matching162534 : Equiv.Perm (Fin 3) := Equiv.swap 0 2

theorem noncrossing124_iff (p : Equiv.Perm (Fin 3)) :
    triple_noncrossing triple124 triple356 p ↔
      p = matching162345 ∨ p = matching162534 := by
  revert p
  decide

theorem noncrossing123_iff (p : Equiv.Perm (Fin 3)) :
    triple_noncrossing triple123 triple456 p ↔ p = matching162534 := by
  revert p
  decide

theorem sign_matching162345 : Equiv.Perm.sign matching162345 = 1 := by
  rw [matching162345, map_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  decide

theorem sign_matching162534 : Equiv.Perm.sign matching162534 = -1 := by
  exact Equiv.Perm.sign_swap (by decide)

/-- The common negative matching is literally the same unordered terminal pairs. -/
theorem common_matching_pairs :
    (Finset.univ.image fun i => s(triple124 i,triple356 (matching162534 i))) =
      (Finset.univ.image fun i => s(triple123 i,triple456 (matching162534 i))) := by
  decide

theorem source_triples_complete :
    Function.Injective triple124 ∧ Function.Injective triple356 ∧
    Disjoint (Set.range triple124) (Set.range triple356) ∧
    Set.range triple124 ∪ Set.range triple356 = Set.univ ∧
    Function.Injective triple123 ∧ Function.Injective triple456 ∧
    Disjoint (Set.range triple123) (Set.range triple456) ∧
    Set.range triple123 ∪ Set.range triple456 = Set.univ := by
  simp only [Function.Injective, Set.disjoint_left, Set.ext_iff, Set.mem_union,
    Set.mem_range, Set.mem_univ]
  decide

end FiniteAvalanches.Electrical.PairFormula


namespace FiniteAvalanches.Electrical.PairFormula
open scoped BigOperators

/-- The three unoriented pairs induced by a bijection of the two triples. -/
def matchingPairs (U W : Fin 3 → Fin 6) (p : Equiv.Perm (Fin 3)) :
    Finset (Sym2 (Fin 6)) := Finset.univ.image fun i => s(U i,W (p i))

theorem signed_noncrossing_difference (Z : Finset (Sym2 (Fin 6)) → ℤ) :
    (∑ p : Equiv.Perm (Fin 3), if triple_noncrossing triple124 triple356 p then
      (Equiv.Perm.sign p : ℤ) * Z (matchingPairs triple124 triple356 p) else 0) -
    (∑ p : Equiv.Perm (Fin 3), if triple_noncrossing triple123 triple456 p then
      (Equiv.Perm.sign p : ℤ) * Z (matchingPairs triple123 triple456 p) else 0) =
    Z (matchingPairs triple124 triple356 matching162345) := by
  have hne : matching162345 ≠ matching162534 := by decide
  have hfirst : (∑ p : Equiv.Perm (Fin 3), if triple_noncrossing triple124 triple356 p then
      (Equiv.Perm.sign p : ℤ) * Z (matchingPairs triple124 triple356 p) else 0) =
      Z (matchingPairs triple124 triple356 matching162345) -
        Z (matchingPairs triple124 triple356 matching162534) := by
    calc
      _ = ∑ p : Equiv.Perm (Fin 3),
          ((if p = matching162345 then Z (matchingPairs triple124 triple356 p) else 0) -
           (if p = matching162534 then Z (matchingPairs triple124 triple356 p) else 0)) := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : p = matching162345
        · subst p; simp [noncrossing124_iff, hne, sign_matching162345]
        · by_cases hq : p = matching162534
          · subst p; simp [noncrossing124_iff, hp, sign_matching162534]
          · simp [noncrossing124_iff, hp, hq]
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  have hsecond : (∑ p : Equiv.Perm (Fin 3), if triple_noncrossing triple123 triple456 p then
      (Equiv.Perm.sign p : ℤ) * Z (matchingPairs triple123 triple456 p) else 0) =
      -Z (matchingPairs triple123 triple456 matching162534) := by
    simp [noncrossing123_iff, sign_matching162534]
  rw [hfirst, hsecond]
  have hpairs : matchingPairs triple124 triple356 matching162534 =
      matchingPairs triple123 triple456 matching162534 := common_matching_pairs
  rw [hpairs]
  ring
end FiniteAvalanches.Electrical.PairFormula
