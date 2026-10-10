import FiniteAvalanches.Trees.ForestProjection.GramTransport
import FiniteAvalanches.Trees.ForestProjection.Deletion
import FiniteAvalanches.Trees.ForestProjection.Uniform
import FiniteAvalanches.Trees.ForestProjection.PrincipalMinors
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Lattice

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Electrical FiniteAvalanches.ForestProjectionAlgebra
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- All avoidance probabilities of the actual uniform original copied-forest law. -/
theorem uniformRootedForestMass_avoidance_det (R : Finset V) (hR : R.Nonempty)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) (A : Finset E) :
    ∑ F : Finset E, Set.indicator {F : Finset E | Disjoint A F}
      (G.uniformRootedForestMass (R : Set V) hR hconn) F =
      (((1 : Matrix E E ℝ) - G.rootProjection R hR
          (G.supportGraph_preconnected_of_reaches hconn)).submatrix
        (Subtype.val : A → E) Subtype.val).det := by
  rw [G.sum_uniformRootedForestMass_event]
  simp only [Set.mem_setOf_eq]
  have he : {F : G.RootedForest (R : Set V) // Disjoint A F.val} ≃
      {F : G.RootedForest (R : Set V) // F.val ⊆ Aᶜ} :=
    Equiv.subtypeEquivRight (fun _ => Finset.subset_compl_iff_disjoint_left.symm)
  rw [Nat.card_congr he, ← G.edgeSubgraph_forest_count]
  rw [← (G.edgeSubgraph Aᶜ).rootGram_det_eq_original_forest_count R hR,
    ← G.rootGram_det_eq_original_forest_count R hR]
  exact (G.rootProjection_avoidance_minor_det R hR
    (G.supportGraph_preconnected_of_reaches hconn) A).symm

/-- Inclusion–exclusion of actual copied-subset events, with no probabilistic input. -/
theorem inclusion_mass_eq_sum_avoidance (p : Finset E → ℝ) (A : Finset E) :
    ∑ F : Finset E, Set.indicator {F : Finset E | A ⊆ F} p F =
      ∑ T ∈ A.powerset, (-1 : ℝ) ^ T.card *
        ∑ F : Finset E, Set.indicator {F : Finset E | Disjoint T F} p F := by
  let missing (e : E) : Finset (Finset E) := Finset.univ.filter (fun F => e ∉ F)
  have hinf (T : Finset E) : T.inf missing =
      Finset.univ.filter (fun F : Finset E => Disjoint T F) := by
    ext F
    simp only [Finset.mem_inf, missing, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.disjoint_left]
  have hcompl : A.inf (fun e => (missing e)ᶜ) =
      Finset.univ.filter (fun F : Finset E => A ⊆ F) := by
    ext F
    simp only [Finset.mem_inf, Finset.mem_compl, missing, Finset.mem_filter,
      Finset.mem_univ, true_and, not_not, Finset.subset_iff]
  have h := Finset.inclusion_exclusion_sum_inf_compl A missing p
  rw [hcompl] at h
  simp_rw [hinf] at h
  simp only [Finset.sum_filter] at h
  have hnorm : (∑ F : Finset E, if A ⊆ F then p F else 0) =
      ∑ T ∈ A.powerset, (-1 : ℝ) ^ T.card *
        ∑ F : Finset E, if Disjoint T F then p F else 0 := by
    simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using h
  calc
    _ = ∑ F : Finset E, if A ⊆ F then p F else 0 := by
      apply Finset.sum_congr rfl
      intro F _
      by_cases hAF : A ⊆ F <;> simp [Set.indicator, hAF]
    _ = _ := hnorm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _
      congr 1
      apply Finset.sum_congr rfl
      intro F _
      by_cases hTF : Disjoint T F <;> simp [Set.indicator, hTF]

/-- The actual original uniform rooted-forest law satisfies every determinant inclusion law. -/
theorem uniformRootedForestMass_inclusion_det (R : Finset V) (hR : R.Nonempty)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) (A : Finset E) :
    ∑ F : Finset E, Set.indicator {F : Finset E | A ⊆ F}
      (G.uniformRootedForestMass (R : Set V) hR hconn) F =
      ((G.rootProjection R hR (G.supportGraph_preconnected_of_reaches hconn)).submatrix
        (Subtype.val : A → E) Subtype.val).det := by
  rw [inclusion_mass_eq_sum_avoidance]
  simp_rw [G.uniformRootedForestMass_avoidance_det R hR hconn]
  exact (det_principal_eq_sum_complementary
    (G.rootProjection R hR (G.supportGraph_preconnected_of_reaches hconn)) A).symm

/-- The same full inclusion law on the exact root-set carrier of the source lemma. -/
theorem uniformRootedForestMass_set_inclusion_det (R : Set V) (hR : R.Nonempty)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) (A : Finset E) :
    ∑ F : Finset E, Set.indicator {F : Finset E | A ⊆ F}
      (G.uniformRootedForestMass R hR hconn) F =
      ((G.rootProjection R.toFinset (Set.toFinset_nonempty.mpr hR)
        (G.supportGraph_preconnected_of_reaches hconn)).submatrix
        (Subtype.val : A → E) Subtype.val).det := by
  have h := G.uniformRootedForestMass_inclusion_det
    R.toFinset (Set.toFinset_nonempty.mpr hR) hconn A
  have hset : (R.toFinset : Set V) = R := Set.coe_toFinset R
  have hm : G.uniformRootedForestMass (R.toFinset : Set V)
      (Set.toFinset_nonempty.mpr hR) hconn = G.uniformRootedForestMass R hR hconn := by
    funext F
    unfold uniformRootedForestMass
    rw [hset]
  rw [hm] at h
  exact h

end FiniteAvalanches.Trees.Multigraph
