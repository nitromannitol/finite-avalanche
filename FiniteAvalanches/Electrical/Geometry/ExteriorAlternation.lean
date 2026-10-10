import FiniteAvalanches.Electrical.Geometry.CellCases

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical
noncomputable section

/-- The exterior of the Euclidean unit circle, including its boundary. -/
def exterior : Set (ℝ × ℝ) := {z | 1 ≤ z.1^2 + z.2^2}
def radiusSq (z : ℝ × ℝ) : ℝ := z.1^2 + z.2^2
def inversion (z : ℝ × ℝ) : ℝ × ℝ := (z.1 / radiusSq z, z.2 / radiusSq z)

theorem radiusSq_inversion (z : ℝ × ℝ) (hz : radiusSq z ≠ 0) :
    radiusSq (inversion z) = 1 / radiusSq z := by
  dsimp [radiusSq,inversion]
  dsimp [radiusSq] at hz
  field_simp

theorem inversion_involutive (z : ℝ × ℝ) (hz : radiusSq z ≠ 0) :
    inversion (inversion z) = z := by
  change (z.1 / radiusSq z / radiusSq (inversion z),
    z.2 / radiusSq z / radiusSq (inversion z)) = z
  rw [radiusSq_inversion z hz]
  ext <;> dsimp <;> field_simp

theorem inversion_injective : Set.InjOn inversion exterior := by
  intro x hx y hy hxy
  have hx0 : radiusSq x ≠ 0 := by dsimp [exterior,radiusSq] at *; linarith
  have hy0 : radiusSq y ≠ 0 := by dsimp [exterior,radiusSq] at *; linarith
  have h := congrArg inversion hxy
  rwa [inversion_involutive x hx0,inversion_involutive y hy0] at h

theorem inversion_continuousOn : ContinuousOn inversion exterior := by
  have hd : Continuous radiusSq := by unfold radiusSq; fun_prop
  have hz : ∀ z ∈ exterior, radiusSq z ≠ 0 := by
    intro z hz
    dsimp [exterior,radiusSq] at *
    linarith
  exact ((continuous_fst.continuousOn.div hd.continuousOn hz).prodMk
    (continuous_snd.continuousOn.div hd.continuousOn hz))

theorem inversion_mem_disk {z : ℝ × ℝ} (hz : z ∈ exterior) : inversion z ∈ disk := by
  have hrad : 1 ≤ radiusSq z := hz
  have hpos : 0 < radiusSq z := lt_of_lt_of_le zero_lt_one hrad
  change radiusSq (inversion z) ≤ 1
  rw [radiusSq_inversion z hpos.ne']
  exact (div_le_one hpos).mpr hrad

/-- The registered disk standard implies the corresponding obstruction in the circle exterior.
No graph embedding or lattice connectivity result is assumed or asserted here. -/
theorem exterior_alternation_impossible (K L : Set (ℝ × ℝ))
    (hK : IsCompact K) (hKc : IsConnected K) (hL : IsCompact L) (hLc : IsConnected L)
    (hKe : K ⊆ exterior) (hLe : L ⊆ exterior) (hKL : Disjoint K L)
    (hE : (1,0) ∈ K) (hW : (-1,0) ∈ K) (hN : (0,1) ∈ L) (hS : (0,-1) ∈ L) : False := by
  have hcK := inversion_continuousOn.mono hKe
  have hcL := inversion_continuousOn.mono hLe
  have hi : Disjoint (inversion '' K) (inversion '' L) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,hxy⟩
    have he : x = y := inversion_injective (hKe hx) (hLe hy) hxy.symm
    exact Set.disjoint_left.mp hKL hx (he ▸ hy)
  apply FiniteAvalanches.External.disk_alternation_impossible
    0 (Real.pi/2) Real.pi (Real.pi/2+Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (inversion '' K) (inversion '' L)
    (hK.image_of_continuousOn hcK) (hKc.image inversion hcK)
    (hL.image_of_continuousOn hcL) (hLc.image inversion hcL)
    (by rintro z ⟨x,hx,rfl⟩; exact inversion_mem_disk (hKe hx))
    (by rintro z ⟨x,hx,rfl⟩; exact inversion_mem_disk (hLe hx)) hi
  · simpa [inversion,radiusSq] using Set.mem_image_of_mem inversion hE
  · simpa [inversion,radiusSq] using Set.mem_image_of_mem inversion hW
  · simpa [inversion,radiusSq] using Set.mem_image_of_mem inversion hN
  · simpa [inversion,radiusSq,Real.cos_add_pi,Real.sin_add_pi] using
      Set.mem_image_of_mem inversion hS

/-- Explicit translated cell normalization sends its four corners to the four axes. -/
def cellCoordinates (o : LatticeProb.Site 2) (x : LatticeProb.Site 2) : ℝ × ℝ :=
  ((x 0 : ℝ) + (x 1 : ℝ) - ((o 0 : ℝ) + (o 1 : ℝ) + 1),
   (x 1 : ℝ) - (x 0 : ℝ) - ((o 1 : ℝ) - (o 0 : ℝ)))

theorem cellCoordinates_corner (o : LatticeProb.Site 2) :
    cellCoordinates o (corner o 0) = (-1,0) ∧
    cellCoordinates o (corner o 1) = (0,-1) ∧
    cellCoordinates o (corner o 2) = (1,0) ∧
    cellCoordinates o (corner o 3) = (0,1) := by
  constructor
  · ext <;> simp [cellCoordinates,corner]
  constructor
  · apply Prod.ext
    all_goals simp [cellCoordinates,corner,LatticeProb.unit]
    all_goals ring
  constructor
  · apply Prod.ext
    all_goals simp [cellCoordinates,corner,LatticeProb.unit]
    all_goals ring
  · apply Prod.ext
    all_goals simp [cellCoordinates,corner,LatticeProb.unit]
    all_goals ring

end
end FiniteAvalanches.Electrical.LatticeCell
