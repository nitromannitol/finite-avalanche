import FiniteAvalanches.Sandpile.Source.RadiusConnector
import FiniteAvalanches.Trees.Lattice.PastTailEstimate

/-! Original ray-edge cuts are actual endpoint pasts. The centered escape
comparison is pointwise on the whole connected one-ended tree carrier. -/
namespace FiniteAvalanches.Sandpile.Source
open LatticeProb MeasureTheory FiniteAvalanches FiniteAvalanches.Sandpile
open SourceCounting Trees.Lattice Trees.Lattice.PastTail TreeMeasurability11
open FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal BigOperators
noncomputable section

theorem supBall_subset_box {r M : ℕ} {x : Site2} (hx : x ∈ boxSites r) :
    supBall x ((M : ℝ) - (r : ℝ)) ⊆ (boxSites M : Set Site2) := by
  intro z hz
  apply (mem_box_sites M z).mpr
  intro i
  have hxi : |x i| ≤ (r : ℤ) := abs_le.mpr ((mem_box_sites r x).mp hx i)
  have hxr : |(x i : ℝ)| ≤ (r : ℝ) := by exact_mod_cast hxi
  have hzi : |(z i : ℝ)| ≤ (M : ℝ) := calc
    |(z i : ℝ)| = |((z i - x i : ℤ) : ℝ) + (x i : ℝ)| := by simp
    _ ≤ |((z i - x i : ℤ) : ℝ)| + |(x i : ℝ)| := abs_add_le _ _
    _ ≤ ((M : ℝ) - (r : ℝ)) + (r : ℝ) := add_le_add (hz i) hxr
    _ = (M : ℝ) := sub_add_cancel _ _
  have hzint : |z i| ≤ (M : ℤ) := by exact_mod_cast hzi
  exact abs_le.mp hzint

/-- Deleting a selected edge on the origin ray gives the outgoing past of
exactly one of its two original endpoints, with no endpoint selected in advance. -/
theorem infinite_cut_component_eq_endpoint_past (T : EndedTree) (f : LatticeEdge)
    (x y : Site2) (hf : f.val = s(x,y))
    (hpath : ∃ n : ℕ, f.val = s((orientedRay T.val T.property.1 T.property.2 0).vertex n,
      (orientedRay T.val T.property.1 T.property.2 0).vertex (n+1))) :
    cutComponent T.val f 0 = vertexPast T.val T.property.1 T.property.2 x ∨
      cutComponent T.val f 0 = vertexPast T.val T.property.1 T.property.2 y := by
  obtain ⟨n, hn⟩ := hpath
  let ray := orientedRay T.val T.property.1 T.property.2 0
  have hstep : ray.vertex (n+1) = towardEnd T.val T.property.1 T.property.2 (ray.vertex n) :=
    infiniteRay_succ T.val T.property.1
      (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) 0 n
  have he : f = outgoingEdge T.val T.property.1 T.property.2 (ray.vertex n) := by
    apply Subtype.ext
    change f.val = s(ray.vertex n, towardEnd T.val T.property.1 T.property.2 (ray.vertex n))
    exact hn.trans (congrArg (fun z => s(ray.vertex n,z)) hstep)
  have ho : (0 : Site2) ∈ vertexPast T.val T.property.1 T.property.2 (ray.vertex n) :=
    (vertexPast_characterization T.val T.property.1 T.property.2 _ _).mpr ⟨n,rfl⟩
  rw [vertexPast_eq_cutComponent, ← he] at ho
  have hc : cutComponent T.val f 0 = vertexPast T.val T.property.1 T.property.2 (ray.vertex n) := by
    rw [vertexPast_eq_cutComponent, ← he]
    exact congrArg SimpleGraph.ConnectedComponent.supp ho
  have hends : ray.vertex n = x ∨ ray.vertex n = y := by
    rcases Sym2.eq_iff.mp (hn.symm.trans hf) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  rcases hends with h | h
  · exact Or.inl (by simpa only [h] using hc)
  · exact Or.inr (by simpa only [h] using hc)

theorem infinite_cut_escape_subset_endpoint_pasts {r M : ℕ} (f : LatticeEdge)
    (x y : Site2) (hf : f.val = s(x,y)) (hx : x ∈ boxSites r) (hy : y ∈ boxSites r) :
    infiniteCutEscape 0 f M ⊆
      Subtype.val ⁻¹' (pastEscapesSup x ((M : ℝ)-(r : ℝ)) ∪
        pastEscapesSup y ((M : ℝ)-(r : ℝ))) := by
  intro T hT
  rcases infinite_cut_component_eq_endpoint_past T f x y hf hT.1 with hc | hc
  · apply Or.inl
    refine (mem_pastEscapesSup_iff T.val T.property.1 T.property.2 x _).mpr ?_
    intro h
    exact hT.2 (hc ▸ (h.trans (supBall_subset_box hx)))
  · apply Or.inr
    refine (mem_pastEscapesSup_iff T.val T.property.1 T.property.2 y _).mpr ?_
    intro h
    exact hT.2 (hc ▸ (h.trans (supBall_subset_box hy)))

/-- One universal past constant controls every fixed original edge whose two
endpoints are in the source square, at every admissible source gap. -/
theorem exists_cut_escape_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (r M : ℕ), r+2 ≤ M →
      ∀ (f : LatticeEdge) (x y : Site2), f.val = s(x,y) →
        x ∈ boxSites r → y ∈ boxSites r →
      endedUST.real (infiniteCutEscape 0 f M) ≤
        2*C*((M : ℝ)-(r : ℝ)) ^ (-(1/3 : ℝ)) := by
  obtain ⟨C,hC,htail⟩ := vertex_past_tail
  refine ⟨C,hC,?_⟩
  intro r M hM f x y hf hx hy
  have hgap : 2 ≤ (M : ℝ)-(r : ℝ) := by exact_mod_cast (show (2 : ℤ) ≤ (M : ℤ)-(r : ℤ) by omega)
  let A := pastEscapesSup x ((M : ℝ)-(r : ℝ))
  let B := pastEscapesSup y ((M : ℝ)-(r : ℝ))
  have hmap : endedUST (Subtype.val ⁻¹' (A ∪ B)) =
      (squareLatticeUST : Measure EdgeField) (A ∪ B) := by
    rw [← endedUST_map, Measure.map_apply measurable_subtype_coe
      ((measurableSet_pastEscapesSup x _).union (measurableSet_pastEscapesSup y _))]
  calc
    endedUST.real (infiniteCutEscape 0 f M) ≤
        endedUST.real (Subtype.val ⁻¹' (A ∪ B)) :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (infinite_cut_escape_subset_endpoint_pasts f x y hf hx hy))
    _ = (squareLatticeUST : Measure EdgeField).real (A ∪ B) := congrArg ENNReal.toReal hmap
    _ ≤ (squareLatticeUST : Measure EdgeField).real A +
        (squareLatticeUST : Measure EdgeField).real B := measureReal_union_le _ _
    _ ≤ C*((M : ℝ)-(r : ℝ)) ^ (-(1/3 : ℝ)) +
        C*((M : ℝ)-(r : ℝ)) ^ (-(1/3 : ℝ)) := add_le_add (htail x _ hgap) (htail y _ hgap)
    _ = _ := by ring

#print axioms infinite_cut_component_eq_endpoint_past
#print axioms exists_cut_escape_bound
end
end FiniteAvalanches.Sandpile.Source
