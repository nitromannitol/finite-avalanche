import FiniteAvalanches.Wilson.Lattice.SimpleWalk
import FiniteAvalanches.Needle.Conductance
import FiniteAvalanches.Sandpile.Components.Incident
import LatticeProb.Walk.HitBeforeFirstStep

namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Sandpile.FiniteWired MeasureTheory
open scoped Classical BigOperators
noncomputable section

theorem driven_position (x : Site 2) (ω : WalkDriver) (n : ℕ) :
    DrivenWalk.position (fun y d => y + step d) x ω n = position x ω n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [DrivenWalk.position_succ, position_succ, ih]

theorem driven_hitBefore (A C : Set (Site 2)) (x : Site 2) :
    DrivenWalk.hitBefore (fun y d => y + step d) A C x = hitBefore A C x := by
  ext ω
  simp only [DrivenWalk.hitBefore, hitBefore, Set.mem_setOf_eq, driven_position]

theorem hitBefore_first_step (A C : Set (Site 2)) (x : Site 2)
    (hxA : x ∉ A) (hxC : x ∉ C) :
    walkLaw (hitBefore A C x) =
      ∑ d : Direction, walkLaw (hitBefore A C (x + step d)) / 4 := by
  have h := DrivenWalk.measure_hitBefore_eq_lintegral directionLaw
    (fun (y : Site 2) d => y + step d) (measurable_of_countable _)
    A C (Set.to_countable A).measurableSet (Set.to_countable C).measurableSet
    x hxA hxC
  simp only [driven_hitBefore, lintegral_fintype] at h
  unfold walkLaw
  rw [h]
  apply Finset.sum_congr rfl
  intro d _
  have hc : Nat.card Direction = 4 := by rw [Nat.card_eq_fintype_card]; decide
  simp only [directionLaw, uniformMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_singleton, mul_one, hc, Nat.cast_ofNat, div_eq_mul_inv]

end
end FiniteAvalanches.Wilson.Lattice

namespace FiniteAvalanches.WiredHitting
open LatticeProb FiniteAvalanches.Sandpile.FiniteWired MeasureTheory
open FiniteAvalanches.Electrical FiniteAvalanches.Wilson.Lattice
open scoped Classical BigOperators
noncomputable section

/-- The literal contraction of the exterior to the wired terminal. -/
def wiredVertex (N : ℕ) (x : Site 2) : Vertex N :=
  if hx : inBox N x then some (activeOfSite N x hx) else none

private def other (N : ℕ) (x : Active N) (e : Edge N) : Vertex N :=
  if (endpoints e).1 = some x then (endpoints e).2 else (endpoints e).1

private theorem other_direction (N : ℕ) (x : Active N) (d : Direction) :
    other N x (directionEdge x d) = wiredVertex N (site x + step d) := by
  rcases d with ⟨i,b⟩
  cases b
  · simp only [step, Bool.false_eq_true, if_false, ← sub_eq_add_neg]
    by_cases hb : inBox N (site x - unit i)
    · have hn := endpoints_ne (directionEdge x (i,false))
      simp only [directionEdge, dif_pos hb, endpoints] at hn
      simp only [other, directionEdge, endpoints, wiredVertex, dif_pos hb, if_neg hn]
    · simp only [other, directionEdge, endpoints, wiredVertex, dif_neg hb, if_true]
  · simp only [step, if_true]
    by_cases hb : inBox N (site x + unit i)
    · simp only [other, directionEdge, endpoints, wiredVertex, dif_pos hb, if_true]
    · simp only [other, directionEdge, endpoints, wiredVertex, dif_neg hb, if_true]

/-- Positive copied-edge Laplacian, reindexed by every original direction once. -/
theorem laplacian_directions (N : ℕ) (f : Vertex N → ℝ) (x : Active N) :
    laplacian (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2) f (some x) =
      ∑ d : Direction, (f (some x) - f (wiredVertex N (site x + step d))) := by
  let I : Finset (Edge N) := Finset.univ.filter (Sandpile.Components.incident x)
  let g : Edge N → ℝ := fun e =>
    (if (endpoints e).1 = some x then f (some x)-f (endpoints e).2 else 0) +
    (if (endpoints e).2 = some x then f (some x)-f (endpoints e).1 else 0)
  have him : I = Finset.univ.image (directionEdge x) := by
    ext e
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · exact Sandpile.Components.exists_direction_of_incident x e
    · rintro ⟨d,rfl⟩
      exact Sandpile.Components.direction_edge_incident x d
  have hz (e : Edge N) (he : e ∉ I) : g e = 0 := by
    have h : ¬Sandpile.Components.incident x e := by simpa [I] using he
    simp only [Sandpile.Components.incident, not_or] at h
    simp only [g, if_neg h.1, if_neg h.2, add_zero]
  have hp (e : Edge N) (he : e ∈ I) : g e = f (some x)-f (other N x e) := by
    have h : Sandpile.Components.incident x e := (Finset.mem_filter.mp he).2
    rcases h with h | h
    · have hn : (endpoints e).2 ≠ some x := fun hh => endpoints_ne e (h.trans hh.symm)
      simp only [g, other, h, if_true, if_neg hn, add_zero]
    · have hn : (endpoints e).1 ≠ some x := fun hh => endpoints_ne e (hh.trans h.symm)
      simp only [g, other, h, if_true, if_neg hn, zero_add]
  have heq : laplacian (fun e : Edge N => (endpoints e).1)
      (fun e => (endpoints e).2) f (some x) = ∑ e : Edge N, g e := by
    unfold laplacian
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [g]
    split_ifs <;> rfl
  rw [heq]
  calc
    _ = ∑ e ∈ I, g e :=
      (Finset.sum_subset (s₁ := I) (s₂ := Finset.univ) (f := g)
        (Finset.subset_univ I) (fun e _ he => hz e he)).symm
    _ = ∑ e ∈ I, (f (some x)-f (other N x e)) := Finset.sum_congr rfl hp
    _ = ∑ d : Direction, (f (some x)-f (other N x (directionEdge x d))) := by
      rw [him, Finset.sum_image]
      exact fun d _ e _ h => Sandpile.Components.direction_edge_injective x h
    _ = _ := Finset.sum_congr rfl (fun d _ => by rw [other_direction])


/-- The real probability, with the exterior wired to the distinguished sink. -/
def hittingVoltage (N : ℕ) (S : Finset (Active N)) : Vertex N → ℝ
  | none => 1
  | some x => (walkLaw (hitBefore (↑(S.image site)) (box 2 N)ᶜ (site x))).toReal

private theorem hitBefore_exterior (N : ℕ) (S : Finset (Active N)) (x : Site 2)
    (hx : x ∉ box 2 N) : hitBefore (↑(S.image site)) (box 2 N)ᶜ x = Set.univ := by
  have hxA : x ∉ (↑(S.image site) : Set (Site 2)) := by
    intro hm
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hm
    exact hx ((inBox_iff N (site y)).mp (fun i => (y i).property))
  rw [← driven_hitBefore]
  exact DrivenWalk.hitBefore_eq_univ _ _ _ _ hxA hx

private theorem hittingVoltage_wiredVertex (N : ℕ) (S : Finset (Active N)) (x : Site 2) :
    hittingVoltage N S (wiredVertex N x) =
      (walkLaw (hitBefore (↑(S.image site)) (box 2 N)ᶜ x)).toReal := by
  by_cases hx : inBox N x
  · rw [wiredVertex, dif_pos hx]
    rfl
  · rw [wiredVertex, dif_neg hx, hittingVoltage,
      hitBefore_exterior N S x (fun h => hx ((inBox_iff N x).mpr h)), measure_univ]
    exact ENNReal.toReal_one.symm

private theorem hittingVoltage_zero (N : ℕ) (S : Finset (Active N)) (x : Active N)
    (hx : x ∈ S) : hittingVoltage N S (some x) = 0 := by
  have he : hitBefore (↑(S.image site)) (box 2 N)ᶜ (site x) = ∅ := by
    rw [← driven_hitBefore]
    exact DrivenWalk.hitBefore_eq_empty _ _ _ _ (Finset.mem_image_of_mem site hx)
  simp only [hittingVoltage, he, measure_empty, ENNReal.toReal_zero]

private theorem hittingVoltage_harmonic (N : ℕ) (S : Finset (Active N)) (x : Active N)
    (hx : x ∉ S) : laplacian (fun e : Edge N => (endpoints e).1)
      (fun e => (endpoints e).2) (hittingVoltage N S) (some x) = 0 := by
  have hxA : site x ∉ (↑(S.image site) : Set (Site 2)) := by
    intro hm
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    exact hx ((site_injective N he) ▸ hy)
  have hxC : site x ∉ (box 2 N)ᶜ := by
    exact fun h => h ((inBox_iff N (site x)).mp (fun i => (x i).property))
  have h := congrArg ENNReal.toReal (hitBefore_first_step
    (↑(S.image site)) (box 2 N)ᶜ (site x) hxA hxC)
  rw [ENNReal.toReal_sum] at h
  · simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat] at h
    rw [laplacian_directions, Finset.sum_sub_distrib]
    simp only [hittingVoltage_wiredVertex]
    have hc : Fintype.card Direction = 4 := by decide
    simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul, Nat.cast_ofNat,
      hittingVoltage]
    rw [← Finset.sum_div] at h
    linarith only [h]
  · intro d _
    exact ENNReal.div_ne_top (measure_ne_top walkLaw _) (by norm_num)

theorem hittingVoltage_eq_voltage (N : ℕ) (S : Finset (Active N)) :
    hittingVoltage N S = Needle.voltage N S := by
  apply Needle.voltage_unique N S
  · rfl
  · exact hittingVoltage_zero N S
  · intro v hv
    cases v with
    | none => exact (hv (Finset.mem_insert_self _ _)).elim
    | some x =>
      apply hittingVoltage_harmonic
      intro hx
      exact hv (Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hx))

/-- The literal full-carrier hitting probability equals the copied-network voltage. -/
theorem wired_srw_firstHit_voltage (N : ℕ) (S : Finset (Active N)) (x : Site 2) :
    walkLaw (hitBefore (↑(S.image site) : Set (Site 2)) (box 2 N)ᶜ x) =
      ENNReal.ofReal (Needle.voltage N S
        (if hx : inBox N x then some (activeOfSite N x hx) else none)) := by
  rw [← wiredVertex, ← hittingVoltage_eq_voltage, hittingVoltage_wiredVertex,
    ENNReal.ofReal_toReal (measure_ne_top walkLaw _)]

end
end FiniteAvalanches.WiredHitting
