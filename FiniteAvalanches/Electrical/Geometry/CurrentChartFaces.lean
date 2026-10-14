import FiniteAvalanches.External.PlaneEdgeChartIncidence
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.BSST.CurrentChartFaces
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- One connected open side of the actual straightening chart. -/
def chartHalf (Q : Drawing J) (e : E) (c : EdgeChart Q e) (positive : Bool) : Set Plane :=
  Set.Ioo (1/2-c.radius) (1/2+c.radius) ×ˢ
    (if positive then Set.Ioo 0 c.radius else Set.Ioo (-c.radius) 0)

/-- Both chart half-boxes avoid the original drawn trace, not just a selected subgraph. -/
theorem chartHalf_off_trace (Q : Drawing J) (e : E) (c : EdgeChart Q e)
    (positive : Bool) (z : Plane) (hz : z ∈ chartHalf Q e c positive) :
    c.chart.map.symm z ∉ drawingTrace Q := by
  have hx : |z.1-1/2| < c.radius := abs_lt.mpr ⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩
  have hy : |z.2| < c.radius := by
    cases positive <;> simp only [chartHalf,Set.mem_prod,↓reduceIte,Set.mem_Ioo] at hz
    · exact abs_lt.mpr ⟨hz.2.1,by linarith [hz.2.2,c.radius_pos]⟩
    · exact abs_lt.mpr ⟨by linarith [hz.2.1,c.radius_pos],hz.2.2⟩
  have hne : z.2 ≠ 0 := by
    cases positive <;> simp only [chartHalf,Set.mem_prod,↓reduceIte,Set.mem_Ioo] at hz
    · exact ne_of_lt hz.2.2
    · exact ne_of_gt hz.2.1
  exact fun ht => hne ((c.trace_box z hx hy).mp ht)

/-- A point on a chart half-box belongs to the actual component of its side point. -/
theorem chartHalf_component (Q : Drawing J) (e : E) (c : EdgeChart Q e)
    (positive : Bool) (z : Plane) (hz : z ∈ chartHalf Q e c positive) :
    ConnectedComponents.mk ⟨c.chart.map.symm z,chartHalf_off_trace Q e c positive z hz⟩ =
      if positive then positiveChartFace Q e c else negativeChartFace Q e c := by
  have hconn : IsPreconnected (chartHalf Q e c positive) := by
    unfold chartHalf
    cases positive <;> exact isPreconnected_Ioo.prod isPreconnected_Ioo
  letI : PreconnectedSpace (chartHalf Q e c positive) := isPreconnected_iff_preconnectedSpace.mp hconn
  let g : chartHalf Q e c positive → {w : Plane // w ∉ drawingTrace Q} :=
    fun w => ⟨c.chart.map.symm w.val,chartHalf_off_trace Q e c positive w.val w.property⟩
  have hg : Continuous g := by
    exact Continuous.subtype_mk (c.chart.map.symm.continuous.comp continuous_subtype_val) _
  let center : Plane := (1/2,if positive then c.radius/2 else -(c.radius/2))
  have hc : center ∈ chartHalf Q e c positive := by
    cases positive <;> simp only [center,chartHalf,Set.mem_prod,Bool.false_eq_true,if_false,if_true,Set.mem_Ioo]
    all_goals constructor <;> constructor <;> linarith [c.radius_pos]
  have heq : ConnectedComponents.mk (g ⟨z,hz⟩) = ConnectedComponents.mk (g ⟨center,hc⟩) := by
    apply ConnectedComponents.coe_eq_coe'.mpr
    exact (isPreconnected_range hg).subset_connectedComponent ⟨⟨center,hc⟩,rfl⟩ ⟨⟨z,hz⟩,rfl⟩
  cases positive <;> exact heq

/-- Any whole-arc incident face is one of the two actual oriented chart sides. -/
theorem edgeFaces_subset_chart (Q : Drawing J) (e : E) (c : EdgeChart Q e)
    (F : Face Q) (hF : F ∈ edgeFaces Q e) :
    F = positiveChartFace Q e c ∨ F = negativeChartFace Q e c := by
  let box : Set Plane := Set.Ioo (1/2-c.radius) (1/2+c.radius) ×ˢ Set.Ioo (-c.radius) c.radius
  let U : Set Plane := c.chart.map ⁻¹' box
  have hU : IsOpen U := (isOpen_Ioo.prod isOpen_Ioo).preimage c.chart.map.continuous
  let midpoint : ArcParameter := ⟨1/2,by constructor <;> norm_num⟩
  have hm : c.chart.map (Q.curve e midpoint) = (1/2,0) :=
    c.straight midpoint (by simpa [midpoint] using c.radius_pos)
  have hmU : Q.curve e midpoint ∈ U := by
    change c.chart.map (Q.curve e midpoint) ∈ box
    rw [hm]
    constructor <;> constructor <;> linarith [c.radius_pos]
  obtain ⟨w,hwU,hwF⟩ := mem_closure_iff.mp (hF ⟨midpoint,rfl⟩) U hU hmU
  obtain ⟨hwtrace,hwface⟩ := hwF
  let z := c.chart.map w
  have hz : z ∈ box := hwU
  have hzne : z.2 ≠ 0 := by
    intro heq
    apply hwtrace
    have hx : |z.1-1/2| < c.radius := abs_lt.mpr ⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩
    have hy : |z.2| < c.radius := abs_lt.mpr hz.2
    have ht := (c.trace_box z hx hy).mpr heq
    simpa only [z,Homeomorph.symm_apply_apply] using ht
  by_cases hp : 0 < z.2
  · have hh : z ∈ chartHalf Q e c true := ⟨hz.1,hp,hz.2.2⟩
    have hcomp := chartHalf_component Q e c true z hh
    have heq : (⟨c.chart.map.symm z,chartHalf_off_trace Q e c true z hh⟩ :
        {w : Plane // w ∉ drawingTrace Q}) = ⟨w,hwtrace⟩ := by
      apply Subtype.ext
      exact c.chart.map.symm_apply_apply w
    rw [heq,hwface] at hcomp
    exact Or.inl hcomp
  · have hn : z.2 < 0 := lt_of_le_of_ne (le_of_not_gt hp) hzne
    have hh : z ∈ chartHalf Q e c false := ⟨hz.1,hz.2.1,hn⟩
    have hcomp := chartHalf_component Q e c false z hh
    have heq : (⟨c.chart.map.symm z,chartHalf_off_trace Q e c false z hh⟩ :
        {w : Plane // w ∉ drawingTrace Q}) = ⟨w,hwtrace⟩ := by
      apply Subtype.ext
      exact c.chart.map.symm_apply_apply w
    rw [heq,hwface] at hcomp
    exact Or.inr hcomp

/-- Exact characterization of whole-arc faces, using only the registered generic incidence input. -/
theorem edgeFaces_iff_chart (Q : Drawing J) (e : E) (c : EdgeChart Q e)
    (hne : J.left e ≠ J.right e) (F : Face Q) :
    F ∈ edgeFaces Q e ↔ F = positiveChartFace Q e c ∨ F = negativeChartFace Q e c := by
  constructor
  · exact edgeFaces_subset_chart Q e c F
  · intro hf
    have h := FiniteAvalanches.External.plane_edge_chart_incidence J Q e c hne
    rcases hf with rfl | rfl
    · exact h.1
    · exact h.2

end
end FiniteAvalanches.Electrical.BSST.CurrentChartFaces
