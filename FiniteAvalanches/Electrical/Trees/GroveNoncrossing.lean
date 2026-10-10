import FiniteAvalanches.Electrical.Geometry.BoundaryOrder
import FiniteAvalanches.Electrical.Trees.PairingGroves
import FiniteAvalanches.Electrical.Geometry.DiskCrossing
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-! Actual copied-grove noncrossing and crossing count zero in a closed disk.
The generic source section is copied byte for byte; whole-disk drawing and
literal six-angle cyclic order remain explicit geometric data. -/
namespace FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical
open scoped Classical BigOperators
noncomputable section

namespace CopiedGraph
variable {V E : Type} (J : CopiedGraph V E)

/-- The actual component of a vertex in an original-copy edge subset. -/
def groveComponent (F : Finset E) (root : V) : Set V :=
  {x | J.reaches F root x}

/-- Keep the original IDs in the component, including their multiplicities. -/
def groveComponentCopies (F : Finset E) (root : V) : Finset E :=
  F.filter (fun e => J.left e ∈ J.groveComponent F root)

/-- Reversing an actual copied walk changes no copy IDs. -/
theorem grove_reaches_symm {F : Finset E} {x y : V} (h : J.reaches F x y) :
    J.reaches F y x := by
  induction h with
  | refl => exact .refl
  | @tail y z h hyz ih =>
    obtain ⟨e, he, hends⟩ := hyz
    apply Relation.ReflTransGen.head _ ih
    exact ⟨e, he, hends.elim (fun h => Or.inr ⟨h.2,h.1⟩)
      (fun h => Or.inl ⟨h.2,h.1⟩)⟩

/-- Component restriction retains both actual endpoints of every selected copy. -/
theorem grove_component_copies_supported (F : Finset E) (root : V) :
    ∀ e ∈ J.groveComponentCopies F root,
      J.left e ∈ J.groveComponent F root ∧ J.right e ∈ J.groveComponent F root := by
  intro e he
  obtain ⟨hes, hl⟩ := Finset.mem_filter.mp he
  exact ⟨hl, hl.tail ⟨e,hes,Or.inl ⟨rfl,rfl⟩⟩⟩

/-- The restriction retains every literal walk from its root. -/
theorem reaches_grove_component_copies {F : Finset E} {root y : V}
    (h : J.reaches F root y) : J.reaches (J.groveComponentCopies F root) root y := by
  induction h with
  | refl => exact .refl
  | @tail y z h hyz ih =>
    obtain ⟨e, he, hends⟩ := hyz
    have hl : J.left e ∈ J.groveComponent F root := by
      rcases hends with hends | hends
      · exact hends.1 ▸ h
      · exact h.tail ⟨e,he,Or.inr ⟨hends.1,rfl⟩⟩
    exact ih.tail ⟨e,Finset.mem_filter.mpr ⟨he,hl⟩,hends⟩

/-- Component disjointness comes from the actual copied reachability relation. -/
theorem grove_components_disjoint {F : Finset E} {x y : V}
    (hxy : ¬J.reaches F x y) :
    Disjoint (J.groveComponent F x) (J.groveComponent F y) := by
  apply Set.disjoint_left.mpr
  intro z hxz hyz
  exact hxy (hxz.trans (J.grove_reaches_symm hyz))
end CopiedGraph

namespace Drawing
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E} (drawing : Drawing J)

/-- Two separated actual copied components cannot join alternating disk terminals. -/
theorem grove_alternating_walks_impossible
    (F : Finset E) (a b c d : V)
    (hab : J.reaches F a b) (hcd : J.reaches F c d) (hac : ¬J.reaches F a c)
    (hvertices : ∀ x, drawing.point x ∈ disk)
    (hedges : ∀ e q, drawing.curve e q ∈ disk)
    (θ₀ θ₁ θ₂ θ₃ : ℝ)
    (h₀₁ : θ₀ < θ₁) (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃)
    (h₃₀ : θ₃ < θ₀ + 2 * Real.pi)
    (pa : drawing.point a = (Real.cos θ₀,Real.sin θ₀))
    (pb : drawing.point b = (Real.cos θ₂,Real.sin θ₂))
    (pc : drawing.point c = (Real.cos θ₁,Real.sin θ₁))
    (pd : drawing.point d = (Real.cos θ₃,Real.sin θ₃)) : False := by
  exact drawing.alternating_walks_impossible (J.grove_components_disjoint hac)
    (J.grove_component_copies_supported F a) (J.grove_component_copies_supported F c)
    a b c d Relation.ReflTransGen.refl Relation.ReflTransGen.refl
    (J.reaches_grove_component_copies hab) (J.reaches_grove_component_copies hcd)
    hvertices hedges θ₀ θ₁ θ₂ θ₃ h₀₁ h₁₂ h₂₃ h₃₀ pa pb pc pd

/-- Every literal paired grove on six cyclically ordered disk terminals is noncrossing. -/
theorem pairing_grove_noncrossing (x : Fin 6 → V)
    (hvertices : ∀ x, drawing.point x ∈ disk)
    (hedges : ∀ e q, drawing.curve e q ∈ disk)
    (horder : cyclic_order drawing x)
    (U W : Fin 3 → Fin 6) (p : Equiv.Perm (Fin 3))
    (F : J.PairingGrove (x ∘ U) (x ∘ W) p) : triple_noncrossing U W p := by
  obtain ⟨θ,hmono,hspan,hpoints⟩ := horder
  have hr (r : Fin 3) : J.reaches F.val (x (U r)) (x (W (p r))) :=
    (F.property.2.2.1 r (p r)).mpr rfl
  have hmin (r : Fin 3) : J.reaches F.val (x (U r)) (x (min (U r) (W (p r)))) := by
    by_cases h : U r ≤ W (p r)
    · rw [min_eq_left h]; exact .refl
    · rw [min_eq_right (le_of_not_ge h)]; exact hr r
  have hmax (r : Fin 3) : J.reaches F.val (x (U r)) (x (max (U r) (W (p r)))) := by
    by_cases h : U r ≤ W (p r)
    · rw [max_eq_right h]; exact hr r
    · rw [max_eq_left (le_of_not_ge h)]; exact .refl
  have hh (r : Fin 3) : J.reaches F.val (x (min (U r) (W (p r))))
      (x (max (U r) (W (p r)))) := (J.grove_reaches_symm (hmin r)).trans (hmax r)
  have hsep (r s : Fin 3) (hrs : r ≠ s) :
      ¬J.reaches F.val (x (min (U r) (W (p r)))) (x (min (U s) (W (p s)))) := by
    intro h
    exact F.property.2.2.2 r s hrs ((hmin r).trans (h.trans (J.grove_reaches_symm (hmin s))))
  have hcontr (r s : Fin 3) (hrs : r ≠ s)
      (h₀₁ : min (U r) (W (p r)) < min (U s) (W (p s)))
      (h₁₂ : min (U s) (W (p s)) < max (U r) (W (p r)))
      (h₂₃ : max (U r) (W (p r)) < max (U s) (W (p s))) : False := by
    have hlast : θ (max (U s) (W (p s))) < θ (min (U r) (W (p r))) + 2 * Real.pi := by
      calc
        _ ≤ θ 5 := hmono.monotone
          (show max (U s) (W (p s)) ≤ (5 : Fin 6) by omega)
        _ < θ 0 + 2 * Real.pi := hspan
        _ ≤ _ := add_le_add (hmono.monotone
          (show (0 : Fin 6) ≤ min (U r) (W (p r)) by omega)) le_rfl
    exact drawing.grove_alternating_walks_impossible F.val _ _ _ _ (hh r) (hh s)
      (hsep r s hrs) hvertices hedges _ _ _ _
      (hmono h₀₁) (hmono h₁₂) (hmono h₂₃) hlast
      (hpoints _) (hpoints _) (hpoints _) (hpoints _)
  intro r s hrs hcross
  rcases hcross with ⟨h₀₁,h₁₂,h₂₃⟩ | ⟨h₀₁,h₁₂,h₂₃⟩
  · exact hcontr r s hrs h₀₁ h₁₂ h₂₃
  · exact hcontr s r hrs.symm h₀₁ h₁₂ h₂₃

/-- The actual paired-grove carrier is empty for a crossing matching. -/
theorem card_pairing_grove_eq_zero_of_crossing (x : Fin 6 → V)
    (hvertices : ∀ x, drawing.point x ∈ disk)
    (hedges : ∀ e q, drawing.curve e q ∈ disk)
    (horder : cyclic_order drawing x)
    (U W : Fin 3 → Fin 6) (p : Equiv.Perm (Fin 3))
    (hcross : ¬triple_noncrossing U W p) :
    Nat.card (J.PairingGrove (x ∘ U) (x ∘ W) p) = 0 := by
  letI : IsEmpty (J.PairingGrove (x ∘ U) (x ∘ W) p) :=
    ⟨fun F => hcross (drawing.pairing_grove_noncrossing x hvertices hedges horder U W p F)⟩
  exact Nat.card_of_isEmpty
end Drawing
end
end FiniteAvalanches.Electrical.StatementGeometry

