import FiniteAvalanches.Trees.Lattice.PastFourPathEvents
import FiniteAvalanches.Trees.Lattice.EuclideanPathTail

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.PastTail
open LatticeProb MeasureTheory FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Trees.Lattice.PastTail
open scoped Classical BigOperators
noncomputable section

/-- The ordinary UST's actual outgoing-edge past has the source sup-norm tail. -/
theorem vertex_past_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Site 2, ∀ m : ℝ, 2 ≤ m →
      (squareLatticeUST : Measure EdgeField).real (pastEscapesSup v m) ≤
        C * m ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C₀, hC₀, htail⟩ := BarlowMasson.dual_adjacent_path_euclidean_tail
  let a : ℝ := -(1 / 3 : ℝ)
  refine ⟨4 * C₀ / (2 : ℝ) ^ a,
    div_pos (mul_pos (by norm_num) hC₀) (Real.rpow_pos_of_pos (by norm_num) a), ?_⟩
  intro v m hm
  have hae : pastEscapesSup v m ≤ᵐ[(squareLatticeUST : Measure EdgeField)]
      ⋃ j : Fin 2 × Bool, adjacentDualEscape v j (m / 2) := by
    filter_upwards [squareLatticeUST_ae_four_path_reduction] with ω hω
    obtain ⟨_, _, _, hω⟩ := hω
    exact hω v m hm
  have hprob : (squareLatticeUST : Measure EdgeField).real (pastEscapesSup v m) ≤
      (squareLatticeUST : Measure EdgeField).real
        (⋃ j : Fin 2 × Bool, adjacentDualEscape v j (m / 2)) :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hae)
  have hfixed : ∀ j : Fin 2 × Bool,
      (squareLatticeUST : Measure EdgeField).real (adjacentDualEscape v j (m / 2)) ≤
        C₀ * (m / 2) ^ a := by
    intro j
    let d := dualBaseInv (incidentBase v j)
    exact htail (d.1 + unit d.2) d.1 (show (lattice 2).Adj (d.1 + unit d.2) d.1 from
      (show (lattice 2).Adj d.1 (d.1 + unit d.2) from ⟨d.2, Or.inl rfl⟩).symm)
      (m / 2) (by linarith only [hm])
  calc
    (squareLatticeUST : Measure EdgeField).real (pastEscapesSup v m) ≤
        (squareLatticeUST : Measure EdgeField).real
          (⋃ j : Fin 2 × Bool, adjacentDualEscape v j (m / 2)) := hprob
    _ ≤ ∑ j : Fin 2 × Bool,
        (squareLatticeUST : Measure EdgeField).real (adjacentDualEscape v j (m / 2)) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin 2 × Bool, C₀ * (m / 2) ^ a :=
      Finset.sum_le_sum fun j _ => hfixed j
    _ = 4 * C₀ * (m / 2) ^ a := by simp; ring
    _ = (4 * C₀ / (2 : ℝ) ^ a) * m ^ (-(1 / 3 : ℝ)) := by
      rw [Real.div_rpow (by linarith only [hm]) (by norm_num)]
      dsimp [a]
      ring

end
end FiniteAvalanches.Trees.Lattice.PastTail
