import FiniteAvalanches.Electrical.Plane.BoundarySplit
import FiniteAvalanches.Electrical.Plane.ZeroSegments
import FiniteAvalanches.Electrical.GroundResponse

/-! Actual segment-midpoint trial values on the literal split network and exact M/4 cancellation. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- Midpoint of the actual nonempty incident-height segment. -/
noncomputable def vertexMidpoint {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (psi : ArcFace R da db → ℝ)
    (x : V) (hx : (incidenceDarts a b x).Nonempty) : ℝ × ℝ :=
  (phi x,(streamMin R da db psi x hx+streamMax R da db psi x hx)/2)

theorem vertexMidpoint_mem {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (psi : ArcFace R da db → ℝ)
    (x : V) (hx : (incidenceDarts a b x).Nonempty) :
    vertexMidpoint R da db phi psi x hx ∈ vertexSegment R da db phi psi x hx := by
  have h := stream_span_nonneg R da db psi x hx
  change phi x ∈ Set.Icc (phi x) (phi x) ∧ _ ∈ Set.Icc _ _
  exact ⟨⟨le_rfl,le_rfl⟩,⟨by dsimp [vertexMidpoint]; linarith only [h],
    by dsimp [vertexMidpoint]; linarith only [h]⟩⟩

/-- Source trial data: prescribed zero/one split terminals, arbitrary value zero at beta,
and the angular function at each actual free-vertex segment midpoint. -/
noncomputable def splitTrial {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ) (psi : ArcFace R da db → ℝ)
    (epsilon y0 : ℝ) : SplitVertex alpha → ℝ
  | .inl x => if x.val = beta then 0 else angular epsilon y0
      (vertexMidpoint R da db phi psi x.val (incidenceDarts_nonempty a b alpha beta hne hc x.val))
  | .inr false => 0
  | .inr true => 1

theorem splitTrial_mem_unitInterval {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ) (psi : ArcFace R da db → ℝ)
    (epsilon y0 : ℝ) (he : 0 < epsilon) (x : SplitVertex alpha) :
    0 ≤ splitTrial R alpha beta hne da db hc phi psi epsilon y0 x ∧
      splitTrial R alpha beta hne da db hc phi psi epsilon y0 x ≤ 1 := by
  cases x with
  | inl x =>
    dsimp only [splitTrial]
    split
    · norm_num
    · exact angular_mem_unitInterval epsilon y0 he _
  | inr k => cases k <;> norm_num [splitTrial]

/-- The actual c01, formed from the proved unique harmonic response on the literal split network. -/
noncomputable def splitConductance {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (alpha beta : V) (hbeta : beta ≠ alpha) (side : E → Bool)
    (hc : (supportGraph a b).Preconnected) : ℝ :=
  -responseEntry (fun e => splitEndpoint alpha side (a e) e)
    (fun e => splitEndpoint alpha side (b e) e) (splitTerminals alpha beta hbeta)
    (split_terminal_reachable a b alpha beta hbeta side hc) 0 1

theorem splitConductance_nonneg {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (alpha beta : V) (hbeta : beta ≠ alpha) (side : E → Bool)
    (hc : (supportGraph a b).Preconnected) : 0 ≤ splitConductance a b alpha beta hbeta side hc :=
  neg_nonneg.mpr (responseEntry_nonpos _ _ _ (splitTerminals_injective alpha beta hbeta) _
    0 1 (by decide))

theorem split_pullback_harmonic {V E : Type*} [Fintype E]
    (a b : E → V) (alpha beta : V) (hbeta : beta ≠ alpha) (side : E → Bool)
    (phi : V → ℝ) (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    ∀ x, x ∉ terminalSet (splitTerminals alpha beta hbeta) →
      laplacian (fun e => splitEndpoint alpha side (a e) e)
        (fun e => splitEndpoint alpha side (b e) e) (fun y => phi (collapse alpha y)) x = 0 := by
  intro x hx
  cases x with
  | inl x =>
    rw [split_laplacian_inl]
    apply hh x.val x.property
    intro hxb
    have he : splitTerminals alpha beta hbeta 2 = Sum.inl x := by
      apply congrArg Sum.inl
      exact Subtype.ext hxb.symm
    exact hx (he ▸ mem_terminalSet (splitTerminals alpha beta hbeta) 2)
  | inr k => cases k with
    | false => exact (hx (mem_terminalSet (splitTerminals alpha beta hbeta) 0)).elim
    | true => exact (hx (mem_terminalSet (splitTerminals alpha beta hbeta) 1)).elim

/-- Exact background cancellation for any literal split trial with the prescribed two values. -/
theorem split_response_le_weightedEnergy {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (alpha beta : V) (hbeta : beta ≠ alpha) (side : E → Bool)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (f : SplitVertex alpha → ℝ) (hf0 : f (.inr false) = 0) (hf1 : f (.inr true) = 1) :
    splitConductance a b alpha beta hbeta side hc ≤
      weightedEnergy (fun e => splitEndpoint alpha side (a e) e)
        (fun e => splitEndpoint alpha side (b e) e) (fun x => 1-phi (collapse alpha x)) f := by
  exact ground_response_upper_bound _ _ (splitTerminals alpha beta hbeta)
    (splitTerminals_injective alpha beta hbeta) (split_terminal_reachable a b alpha beta hbeta side hc)
    (fun x => phi (collapse alpha x)) f hp0 hp0 hp1 hf0 hf1
    (split_pullback_harmonic a b alpha beta hbeta side phi hh)

/-- The source trial has precisely M/4 as its background energy, with M counted over original copies once. -/
theorem split_trial_energy_eq {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (alpha beta : V) (hbeta : beta ≠ alpha) (side : E → Bool)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (f : SplitVertex alpha → ℝ) (hf0 : f (.inr false) = 0) (hf1 : f (.inr true) = 1) :
    energy (fun e => splitEndpoint alpha side (a e) e) (fun e => splitEndpoint alpha side (b e) e)
      (fun x => (1/2 : ℝ)+(1-phi (collapse alpha x))*(f x-1/2)) =
      energy a b phi/4 + weightedEnergy (fun e => splitEndpoint alpha side (a e) e)
        (fun e => splitEndpoint alpha side (b e) e) (fun x => 1-phi (collapse alpha x)) f := by
  have hh' := split_pullback_harmonic a b alpha beta hbeta side phi hh
  have h := ground_trial_energy_of_voltage (fun e => splitEndpoint alpha side (a e) e)
    (fun e => splitEndpoint alpha side (b e) e) (fun x => phi (collapse alpha x)) f
    (.inr false) (.inr true) (.inl ⟨beta,hbeta⟩) (by simp) hp0 hp0 hp1 hf0 hf1
    (by
      intro x hx0 hx1 hx2
      apply hh' x
      intro hx
      obtain ⟨i,hi⟩ := (mem_terminalSet_iff (splitTerminals alpha beta hbeta) x).mp hx
      fin_cases i
      · exact hx0 hi.symm
      · exact hx1 hi.symm
      · exact hx2 hi.symm)
  rw [split_energy_pullback] at h
  exact h

/-- Every actual alpha midpoint has the value prescribed at its literal ordered split terminal. -/
theorem splitTrial_alpha_midpoint {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (he : ∀ e, a e ≠ b e)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ) (hpa : phi alpha = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi (energy a b phi) z)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0)
    (hs : ∀ i, 0 < alphaCurrentSequence R alpha beta hne da db ha hb phi i)
    (j0 j1 : Fin (incidenceCount a b alpha)) (hj : j0.val+1 = j1.val)
    (i : Fin (incidenceCount a b alpha)) :
    let s := alphaCurrentSequence R alpha beta hne da db ha hb phi
    let epsilon := min (s j0) (s j1)/10
    let y0 := boundaryHeight s j1.val
    let e := (alphaEnumeration R alpha beta hne da db ha hb i).val.1
    splitTrial R alpha beta hne da db hc phi psi epsilon y0
      (.inr (orderedSide R alpha beta hne da db ha hb j1.val e)) =
        angular epsilon y0 (sideMidpoint R da db phi psi
          (alphaEnumeration R alpha beta hne da db ha hb i).val) := by
  intro s epsilon y0 e
  have hv := alpha_midpoint_value R alpha beta hne da db ha hb phi hpa psi hp h0 hs j0 j1 hj i
  have hside := orderedSide_enumeration R alpha beta hne da db ha hb he j1.val i
  by_cases hi : i.val < j1.val
  · have hf : orderedSide R alpha beta hne da db ha hb j1.val e = false :=
      Bool.eq_false_of_not_eq_true (fun h => (not_le_of_gt hi) (hside.mp h))
    rw [if_pos hi] at hv
    rw [hf]
    exact hv.symm
  · have ht : orderedSide R alpha beta hne da db ha hb j1.val e = true := hside.mpr (by omega)
    rw [if_neg hi] at hv
    rw [ht]
    exact hv.symm

end FiniteAvalanches.Electrical.Plane
