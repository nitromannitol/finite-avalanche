import FiniteAvalanches.Electrical.ForestColor.Voltage
import FiniteAvalanches.Electrical.Reference.ForestRelabel

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment
open LatticeProb ForestColor
open scoped Classical BigOperators
noncomputable section
variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)

abbrev Forest := (StatementTypes.graph D P marked).RootedForest
  ({alpha D P, beta D P} : Set (Vertex D P))

/-- Literal color fraction under the full original copied-forest uniform law. -/
def vertexColorMass (x : Vertex D P) : ℝ :=
  (Nat.card {F : Forest D P marked //
    (StatementTypes.graph D P marked).reaches F.val x (beta D P)} : ℝ) /
    (Nat.card (Forest D P marked) : ℝ)

/-- Relabeling retains the original subset and the full original sample count. -/
def forestEnumeration : Forest D P marked ≃
    ForestColor.Forest ((StatementTypes.graph D P marked).relabelVertices (vertexEnumeration D P)) := by
  let ρ := vertexEnumeration D P
  let R : Finset (Vertex D P) := {alpha D P, beta D P}
  have hR : R.map ρ.toEmbedding = rootPair (0 : Fin (Fintype.card {x : D // x ∉ P.val} + 1)) := by
    simp [R, ρ, rootPair]
  apply Equiv.subtypeEquivRight
  intro F
  have h := (StatementTypes.graph D P marked).relabelVertices_rootedForest_iff ρ R F
  rw [hR] at h
  simpa only [R, Finset.coe_insert, Finset.coe_singleton] using h.symm

theorem colorMass_transport (x : Vertex D P) :
    vertexColorMass D P marked x =
      ForestColor.colorMass ((StatementTypes.graph D P marked).relabelVertices
        (vertexEnumeration D P)) (vertexEnumeration D P x) := by
  let e := forestEnumeration D P marked
  have he : {F : Forest D P marked //
      (StatementTypes.graph D P marked).reaches F.val x (beta D P)} ≃
      {F : ForestColor.Forest ((StatementTypes.graph D P marked).relabelVertices
          (vertexEnumeration D P)) //
        ((StatementTypes.graph D P marked).relabelVertices (vertexEnumeration D P)).reaches
          F.val (vertexEnumeration D P x) 1} := by
    apply Equiv.subtypeEquiv e
    intro F
    have h := (StatementTypes.graph D P marked).relabelVertices_reaches_iff
      (vertexEnumeration D P) F.val x (beta D P)
    have heval : (e F).val = F.val := rfl
    rw [heval]
    simpa only [vertexEnumeration_beta] using h.symm
  unfold vertexColorMass ForestColor.colorMass
  rw [Nat.card_congr he, Nat.card_congr e]

/-- The genuine original finite forest color marginal is the repaired unique voltage. -/
theorem vertexColorMass_eq_voltage
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (x : Vertex D P) :
    vertexColorMass D P marked x = Repair8.voltage D P hD marked x := by
  let ρ := vertexEnumeration D P
  let G := StatementTypes.graph D P marked
  let J := G.relabelVertices ρ
  let phi : Fin (Fintype.card {x : D // x ∉ P.val} + 2) → ℝ :=
    fun y => Repair8.voltage D P hD marked (ρ.symm y)
  have hconn : ∀ u v, J.reaches Finset.univ u v := by
    intro u v
    have h := (G.relabelVertices_reaches_iff ρ Finset.univ (ρ.symm u) (ρ.symm v)).mpr
      (Repair8.graph_reaches D P hD marked _ _)
    simpa only [Equiv.apply_symm_apply] using h
  have ha : ρ.symm 0 = alpha D P := by
    apply ρ.injective
    simp [ρ]
  have hb : ρ.symm 1 = beta D P := by
    apply ρ.injective
    simp [ρ]
  have hs := Repair8.voltage_spec D P hD marked
  have hphi0 : phi 0 = 0 := by simpa only [phi, ha] using hs.1
  have hphi1 : phi 1 = 1 := by simpa only [phi, hb] using hs.2.1
  have hphiH : ∀ y, y ≠ 0 → y ≠ 1 → laplacian J.left J.right phi y = 0 := by
    intro y hy0 hy1
    have h0 : ρ.symm y ≠ alpha D P := by
      intro he
      apply hy0
      simpa only [ρ, vertexEnumeration_alpha, Equiv.apply_symm_apply] using congrArg ρ he
    have h1 : ρ.symm y ≠ beta D P := by
      intro he
      apply hy1
      simpa only [ρ, vertexEnumeration_beta, Equiv.apply_symm_apply] using congrArg ρ he
    have hl := relabel_laplacian G ρ (Repair8.voltage D P hD marked) (ρ.symm y)
    simp only [Equiv.apply_symm_apply] at hl
    exact hl.trans (hs.2.2 _ h0 h1)
  have h := congrFun (ForestColor.colorMass_eq_voltage J hconn phi hphi0 hphi1 hphiH) (ρ x)
  rw [colorMass_transport]
  simpa only [phi, Equiv.symm_apply_apply] using h

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment
