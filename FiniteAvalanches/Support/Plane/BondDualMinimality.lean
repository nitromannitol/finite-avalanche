import FiniteAvalanches.Support.Plane.BondDualReachability
import FiniteAvalanches.Electrical.Geometry.BoundaryPathOrder
import FiniteAvalanches.Electrical.Trees.GroveNoncrossing

/-!
# Minimality of a dual walk around a bond

When both sides of a vertex cut are connected, the noncrossing copies together
with any one crossing copy connect the primal graph. Edge-path duality then
forces a dual walk around a marked crossing to use every other crossing copy.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- Noncrossing copies and one crossing connect a graph whose two cut sides are connected. -/
theorem CopiedGraph.reaches_of_connected_sides (J : CopiedGraph V E) (A : Finset V)
    (hA : ∀ x y : V, x ∈ A → y ∈ A →
      J.reaches (Finset.univ.filter fun e => J.left e ∈ A ∧ J.right e ∈ A) x y)
    (hAc : ∀ x y : V, x ∉ A → y ∉ A →
      J.reaches (Finset.univ.filter fun e => J.left e ∉ A ∧ J.right e ∉ A) x y)
    (S : Finset E) (hS : ∀ e : E, ¬ J.Crosses A e → e ∈ S)
    (f : E) (hf : f ∈ S) (hcross : J.Crosses A f) (x y : V) : J.reaches S x y := by
  classical
  have hin : ∀ x y : V, x ∈ A → y ∈ A → J.reaches S x y := by
    intro u v hu hv
    apply J.reaches_mono ?_ (hA u v hu hv)
    intro e he
    obtain ⟨_, hl, hr⟩ := Finset.mem_filter.mp he
    apply hS e
    rintro (⟨_, hn⟩ | ⟨_, hn⟩)
    · exact hn hr
    · exact hn hl
  have hout : ∀ x y : V, x ∉ A → y ∉ A → J.reaches S x y := by
    intro u v hu hv
    apply J.reaches_mono ?_ (hAc u v hu hv)
    intro e he
    obtain ⟨_, hl, hr⟩ := Finset.mem_filter.mp he
    apply hS e
    rintro (⟨hm, _⟩ | ⟨hm, _⟩)
    · exact hl hm
    · exact hr hm
  have hstep : J.reaches S (J.left f) (J.right f) := .single ⟨f, hf, Or.inl ⟨rfl, rfl⟩⟩
  rcases hcross with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · exact hin x y hx hy
    · exact (hin x (J.left f) hx hl).trans (hstep.trans (hout (J.right f) y hr hy))
    · exact (hout x (J.right f) hx hr).trans
        ((J.grove_reaches_symm hstep).trans (hin (J.left f) y hl hy))
    · exact hout x y hx hy
  · by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · exact hin x y hx hy
    · exact (hin x (J.right f) hx hr).trans
        ((J.grove_reaches_symm hstep).trans (hout (J.left f) y hl hy))
    · exact (hout x (J.left f) hx hl).trans (hstep.trans (hin (J.right f) y hr hy))
    · exact hout x y hx hy

/-- Every dual walk around one edge of a bond uses every other edge of that bond. -/
theorem dual_path_contains_all_bond_edges {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) (A : Finset V)
    (hA : ∀ x y : V, x ∈ A → y ∈ A →
      J.reaches (Finset.univ.filter fun e => J.left e ∈ A ∧ J.right e ∈ A) x y)
    (hAc : ∀ x y : V, x ∉ A → y ∉ A →
      J.reaches (Finset.univ.filter fun e => J.left e ∉ A ∧ J.right e ∉ A) x y)
    (marked : E) (hmarked : J.Crosses A marked) (S : Finset E)
    (hSm : marked ∉ S) (hScut : ∀ f ∈ S, J.Crosses A f)
    (hdual : (⟨fun e => negativeChartFace D e (charts e),
      fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches S
        (negativeChartFace D marked (charts marked)) (positiveChartFace D marked (charts marked))) :
    ∀ f : E, f ≠ marked → J.Crosses A f → f ∈ S := by
  classical
  letI : Nonempty E := ⟨marked⟩
  intro f hfm hf
  by_contra hfS
  let T : Finset E := Sᶜ.erase marked
  have hmT : marked ∉ T := Finset.notMem_erase _ _
  have hnon : ∀ e : E, ¬ J.Crosses A e → e ∈ T := by
    intro e he
    apply Finset.mem_erase.mpr
    constructor
    · intro hem
      subst e
      exact he hmarked
    · exact Finset.mem_compl.mpr (fun heS => he (hScut e heS))
  have hfT : f ∈ T := Finset.mem_erase.mpr ⟨hfm, Finset.mem_compl.mpr hfS⟩
  have hp := J.reaches_of_connected_sides A hA hAc T hnon f hfT hf
    (J.left marked) (J.right marked)
  have hsub : S ⊆ Tᶜ.erase marked := by
    intro e he
    apply Finset.mem_erase.mpr
    constructor
    · intro hem
      subst e
      exact hSm he
    · apply Finset.mem_compl.mpr
      intro heT
      exact (Finset.mem_compl.mp (Finset.mem_erase.mp heT).2) he
  have hd := (⟨fun e => negativeChartFace D e (charts e),
      fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches_mono hsub hdual
  exact ((edge_path_duality D charts T marked hmT).mp hp) hd

end FiniteAvalanches.Electrical.StatementGeometry
