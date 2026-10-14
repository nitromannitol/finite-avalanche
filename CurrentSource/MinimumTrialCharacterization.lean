import CurrentSource.MinimumCornerTransfer
import FiniteAvalanches.Electrical.Physical.Undilated.Meaning

/-! Attained minimum and complete trial characterization in the oriented height coordinate. -/

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Geometry
open CurrentRegularPhysical
open scoped Classical
noncomputable section

variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked)) (A : OuterArc Q (alpha D P) (beta D P))

include hD in
/-- The infimum in the trial is attained on the actual finite incident face star. -/
theorem minimumPoint_height_spec (phi : Vertex D P → ℝ) (H : A.embedding.Face → ℝ)
    (x : {x : D // x ∉ P.val}) :
    (∃ F : A.embedding.Face, incident A.embedding.drawing (.inr x) F ∧
      H F = (minimumPoint D P marked Q A phi H (.inr x)).2) ∧
    ∀ F : A.embedding.Face, incident A.embedding.drawing (.inr x) F →
      (minimumPoint D P marked Q A phi H (.inr x)).2 ≤ H F := by
  let xc : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} :=
    ⟨.inr x,by simp [alpha,beta]⟩
  obtain ⟨_hf,_hn,F,_G,hF,_hG,hlo,_hhi,hmin,_hmax,_hsegment⟩ :=
    PhysicalFaceStar14.physical_incident_values_extrema (sourceGraph D P marked) Q
      (Repair8.graph_connected D P hD marked).preconnected (alpha D P) (beta D P) A H xc
  change (∃ F, incident A.embedding.drawing xc.val F ∧
      H F = sInf (incidentValues A.embedding.drawing H xc.val)) ∧
    ∀ F, incident A.embedding.drawing xc.val F →
      sInf (incidentValues A.embedding.drawing H xc.val) ≤ H F
  refine ⟨⟨F,hF,hmin.symm⟩,?_⟩
  intro G hG
  rw [hmin]
  exact hlo.2 ⟨G,hG,rfl⟩

include hD in
/-- Any attained incident minimum has the same numerical height, including ties. -/
theorem minimumPoint_height_unique (phi : Vertex D P → ℝ) (H : A.embedding.Face → ℝ)
    (x : {x : D // x ∉ P.val}) (y : ℝ)
    (hy : (∃ F, incident A.embedding.drawing (.inr x) F ∧ H F = y) ∧
      ∀ F, incident A.embedding.drawing (.inr x) F → y ≤ H F) :
    y = (minimumPoint D P marked Q A phi H (.inr x)).2 := by
  obtain ⟨⟨F,hF,hFy⟩,hmin⟩ := minimumPoint_height_spec D P marked hD Q A phi H x
  obtain ⟨G,hG,hGy⟩ := hy.1
  exact le_antisymm (hFy ▸ hy.2 F hF) (hGy ▸ hmin G hG)

include hD in
/-- A negative height orientation uses the raw maximum, rather than the raw minimum. -/
theorem minimumPoint_signed_gauge_height (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (sigma : ℝ) (hs : sigma = 1 ∨ sigma = -1)
    (gauge : ℝ) (x : {x : D // x ∉ P.val}) :
    (minimumPoint D P marked Q A phi (fun F => sigma*(psi F-gauge)) (.inr x)).2 =
      if sigma = 1 then sInf (incidentValues A.embedding.drawing psi (.inr x))-gauge
      else gauge-sSup (incidentValues A.embedding.drawing psi (.inr x)) := by
  let xc : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} :=
    ⟨.inr x,by simp [alpha,beta]⟩
  obtain ⟨_hf,_hn,F,G,hF,hG,hlo,hhi,hmin,hmax,_hsegment⟩ :=
    PhysicalFaceStar14.physical_incident_values_extrema (sourceGraph D P marked) Q
      (Repair8.graph_connected D P hD marked).preconnected (alpha D P) (beta D P) A psi xc
  rcases hs with rfl | rfl
  · simp only [one_mul,if_true]
    apply Eq.symm
    apply minimumPoint_height_unique D P marked hD Q A phi (fun F => psi F-gauge) x
    refine ⟨⟨F,hF,?_⟩,?_⟩
    · rw [hmin]
    · intro K hK
      rw [hmin]
      exact sub_le_sub_right (hlo.2 ⟨K,hK,rfl⟩) gauge
  · simp only [neg_one_mul,if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    apply Eq.symm
    apply minimumPoint_height_unique D P marked hD Q A phi (fun F => -(psi F-gauge)) x
    refine ⟨⟨G,hG,?_⟩,?_⟩
    · rw [hmax]; ring
    · intro K hK
      rw [hmax]
      have h := hhi.2 ⟨K,hK,rfl⟩
      linarith only [h]

/-- The complete source formula determines the same trial on every split vertex. -/
theorem splitMinimumTrial_unique (phi : Vertex D P → ℝ) (H : A.embedding.Face → ℝ)
    (epsilon y0 : ℝ) (f : SplitVertex (alpha D P) → ℝ)
    (hf0 : f (.inr false) = 0) (hf1 : f (.inr true) = 1)
    (hfb : f (.inl ⟨beta D P,by simp [alpha,beta]⟩) = 0)
    (hfx : ∀ x : {x : D // x ∉ P.val},
      f (.inl ⟨.inr x,by simp [alpha]⟩) =
        angular epsilon y0 (minimumPoint D P marked Q A phi H (.inr x))) :
    f = splitMinimumTrial D P marked Q A phi H epsilon y0 := by
  funext v
  cases v with
  | inr b => cases b <;> assumption
  | inl v =>
    rcases v with ⟨v,hv⟩
    cases v with
    | inl b =>
      cases b
      · exact (hv rfl).elim
      · simpa [splitMinimumTrial,beta] using hfb
    | inr x =>
      simpa [splitMinimumTrial,beta] using hfx x

/-- The actual trial evaluates the author's scaled angular function at its attained minimum. -/
theorem splitMinimumTrial_scaled_spec (H : A.embedding.Face → ℝ) (p y0 : ℝ) (hp : 0 < p)
    (x : {x : D // x ∉ P.val}) :
    ∃ F : A.embedding.Face, incident A.embedding.drawing (.inr x) F ∧
      (∀ G, incident A.embedding.drawing (.inr x) G → H F ≤ H G) ∧
      splitMinimumTrial D P marked Q A (Repair8.voltage D P hD marked) H (p/2) y0
        (.inl ⟨.inr x,by simp [alpha]⟩) =
      1/2 + ((2/p)*(H F-y0)) /
        (2*max 1 (max |(2/p)*Repair8.voltage D P hD marked (.inr x)| |(2/p)*(H F-y0)|)) := by
  obtain ⟨⟨F,hF,hheight⟩,hmin⟩ := minimumPoint_height_spec D P marked hD Q A
    (Repair8.voltage D P hD marked) H x
  refine ⟨F,hF,?_,?_⟩
  · intro G hG
    rw [hheight]
    exact hmin G hG
  · have hpoint : minimumPoint D P marked Q A (Repair8.voltage D P hD marked) H (.inr x) =
        (Repair8.voltage D P hD marked (.inr x),H F) := by
      apply Prod.ext
      · rfl
      · exact hheight.symm
    simp only [splitMinimumTrial,beta,Sum.inr_ne_inl,if_false,hpoint]
    exact Physical.Undilated.angular_half_current_eq_literal_scaled p y0 hp _

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
