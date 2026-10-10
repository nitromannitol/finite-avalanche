import FiniteAvalanches.Trees.ConnectorCompletion
import FiniteAvalanches.Trees.Measure

/-! Uniform trees containing a fixed copied connector have the exact uniform
rooted-forest completion counts, with every original edge retained. -/
set_option autoImplicit false
namespace FiniteAvalanches.Trees.Multigraph
open MeasureTheory
open scoped Classical ENNReal
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Restrict the actual completion bijection to any event of original copies. -/
def connectorCompletionEventEquiv (R : Set V) (H : Finset E)
    (hH : G.is_tree R H) (A : Set (Finset E)) :
    {t : G.SpanningTree // H ⊆ t.val ∧ t.val \ H ∈ A} ≃
      {F : G.RootedForest R // F.val ∈ A} := by
  let eA :
      {t : {t : G.SpanningTree // H ⊆ t.val} // t.val.val \ H ∈ A} ≃
        {F : G.RootedForest R // F.val ∈ A} :=
    (G.connectorCompletionEquiv R H hH).subtypeEquiv (fun _ => Iff.rfl)
  exact (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun t : G.SpanningTree => H ⊆ t.val)
    (fun t : G.SpanningTree => t.val \ H ∈ A)).symm.trans eA

/-- The numerator counts original copied forests, not distinct color fields. -/
theorem card_connector_completion_event (R : Set V) (H : Finset E)
    (hH : G.is_tree R H) (A : Set (Finset E)) :
    Nat.card {t : G.SpanningTree // H ⊆ t.val ∧ t.val \ H ∈ A} =
      Nat.card {F : G.RootedForest R // F.val ∈ A} :=
  Nat.card_congr (G.connectorCompletionEventEquiv R H hH A)

variable [Nonempty G.SpanningTree]

/-- A genuinely prescribed tree supplies a positive conditioning atom. -/
theorem treeLaw_containing_connector_pos (H : Finset E)
    (t₀ : G.SpanningTree) (hHt : H ⊆ t₀.val) :
    0 < G.treeLaw {t | H ⊆ t.val} := by
  letI : Nonempty {t : G.SpanningTree // H ⊆ t.val} := ⟨⟨t₀,hHt⟩⟩
  rw [show G.treeLaw {t | H ⊆ t.val} =
    (Nat.card {t : G.SpanningTree // H ⊆ t.val} : ℝ≥0∞) / Nat.card G.SpanningTree from
      FiniteAvalanches.uniformMeasure_apply _ _]
  exact ENNReal.div_pos (by exact_mod_cast (Nat.card_pos (α :=
    {t : G.SpanningTree // H ⊆ t.val})).ne') (ENNReal.natCast_ne_top _)

/-- Exact joint/conditioning-atom identity on the actual uniform copied tree law.
The forest denominator is the entire completion carrier. -/
theorem treeLaw_joint_containing_connector (R : Set V) (H : Finset E)
    (hH : G.is_tree R H) (t₀ : G.SpanningTree) (hHt : H ⊆ t₀.val)
    (A : Set (Finset E)) :
    G.treeLaw {t | H ⊆ t.val ∧ t.val \ H ∈ A} =
      G.treeLaw {t | H ⊆ t.val} *
        ((Nat.card {F : G.RootedForest R // F.val ∈ A} : ℝ≥0∞) /
          Nat.card (G.RootedForest R)) := by
  letI : Nonempty (G.RootedForest R) :=
    ⟨G.connectorCompletionEquiv R H hH ⟨t₀,hHt⟩⟩
  have hn : (Nat.card (G.RootedForest R) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G.RootedForest R)).ne'
  rw [show G.treeLaw {t | H ⊆ t.val ∧ t.val \ H ∈ A} =
      (Nat.card {t : G.SpanningTree // H ⊆ t.val ∧ t.val \ H ∈ A} : ℝ≥0∞) /
        Nat.card G.SpanningTree from FiniteAvalanches.uniformMeasure_apply _ _,
    show G.treeLaw {t | H ⊆ t.val} =
      (Nat.card {t : G.SpanningTree // H ⊆ t.val} : ℝ≥0∞) / Nat.card G.SpanningTree from
        FiniteAvalanches.uniformMeasure_apply _ _,
    G.card_connector_completion_event R H hH A, G.card_connector_completions R H hH]
  simp only [div_eq_mul_inv]
  calc
    _ = _ * 1 := (mul_one _).symm
    _ = _ * ((Nat.card (G.RootedForest R) : ℝ≥0∞) *
        (Nat.card (G.RootedForest R) : ℝ≥0∞)⁻¹) := by
      rw [ENNReal.mul_inv_cancel hn (ENNReal.natCast_ne_top _)]
    _ = _ := by ac_rfl

/-- Every original-copy statistic has the resulting finite conditional law. -/
theorem treeLaw_joint_connector_count (R : Set V) (H : Finset E)
    (hH : G.is_tree R H) (t₀ : G.SpanningTree) (hHt : H ⊆ t₀.val)
    (count : Finset E → ℕ) (D : Set ℕ) :
    G.treeLaw {t | H ⊆ t.val ∧ count (t.val \ H) ∈ D} =
      G.treeLaw {t | H ⊆ t.val} *
        ((Nat.card {F : G.RootedForest R // count F.val ∈ D} : ℝ≥0∞) /
          Nat.card (G.RootedForest R)) :=
  G.treeLaw_joint_containing_connector R H hH t₀ hHt (count ⁻¹' D)

end
end FiniteAvalanches.Trees.Multigraph
