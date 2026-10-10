import FiniteAvalanches.Electrical.Green.Positive
import FiniteAvalanches.Electrical.Green.Voltage
import FiniteAvalanches.Electrical.Green.PairBound

/-! Finite boundary restrictions of the actual grounded Green kernel. -/
namespace FiniteAvalanches.Electrical
open scoped BigOperators Classical
variable {V E : Type*} [Fintype V] [Fintype E]

/-- Restriction to an actual finite vertex sequence ending at the grounded vertex. -/
theorem groundedGreen_boundaryPairSum_eq {m : ℕ} (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (w : Fin (m+1) → V) (hw : w (Fin.last m) = v) :
    let G := fun i j => groundedGreen a b v hc (w i) (w j)
    boundaryPairSum G =
      (∑ i : Fin m, (G 0 i.castSucc-G 0 i.succ)*
        (G i.castSucc i.castSucc+G i.succ i.succ+G i.castSucc i.succ))-(G 0 0)^2 := by
  intro G
  apply boundaryPairSum_eq G
  · intro i j; exact groundedGreen_symm a b v hc (w i) (w j)
  · intro j
    dsimp only [G]
    rw [hw,groundedGreen_ground_source]
    rfl

/-- The only remaining sign input is the actual consecutive Green drop, not a moment conclusion. -/
theorem groundedGreen_boundaryPairSum_le {m : ℕ} (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (w : Fin (m+1) → V) (hw : w (Fin.last m) = v)
    (hp : ∀ i : Fin m, 0 ≤ groundedGreen a b v hc (w 0) (w i.castSucc)-groundedGreen a b v hc (w 0) (w i.succ)) :
    let G := fun i j => groundedGreen a b v hc (w i) (w j)
    boundaryPairSum G ≤ (G 0 0)^2/2 + (3/2 : ℝ)*∑ i : Fin m,
      (G 0 i.castSucc-G 0 i.succ)*
        ((G i.castSucc i.castSucc-G 0 i.castSucc)+(G i.succ i.succ-G 0 i.succ)) := by
  intro G
  apply boundaryPairSum_le_of_posSemidef G ((groundedGreen_posSemidef a b v hc).submatrix w)
  · intro j
    dsimp only [G]
    rw [hw,groundedGreen_ground_source]
    rfl
  · exact hp

/-- Both endpoint W-values vanish; every actual W is nonnegative; all drops telescope to M. -/
theorem groundedGreen_boundary_data {m : ℕ} (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (w : Fin (m+1) → V) (hw : w (Fin.last m) = v) :
    let G := fun i j => groundedGreen a b v hc (w i) (w j)
    (∑ i : Fin m, (G 0 i.castSucc-G 0 i.succ)) = G 0 0 ∧
      G 0 0-G 0 0 = 0 ∧ G (Fin.last m) (Fin.last m)-G 0 (Fin.last m) = 0 ∧
      ∀ i, 0 ≤ G i i-G 0 i := by
  intro G
  have hm : G 0 (Fin.last m) = 0 := by dsimp only [G]; rw [hw,groundedGreen_ground]
  have hmm : G (Fin.last m) (Fin.last m) = 0 := by dsimp only [G]; rw [hw,groundedGreen_ground]
  refine ⟨?_,sub_self _,by rw [hm,hmm,sub_self],?_⟩
  · simpa only [hm,sub_zero] using sum_sub_succ m (G 0)
  · intro i; exact groundedGreen_diag_sub_source_nonneg a b v hc (w 0) (w i)

/-- The zero-length restriction really is the grounded singleton, with M and pair sum both zero. -/
theorem boundaryPairSum_zero_length (G : Fin 1 → Fin 1 → ℝ) (hg : ∀ j, G 0 j = 0) :
    boundaryPairSum G = 0 ∧ G 0 0 = 0 := by
  exact ⟨by simp [boundaryPairSum],hg 0⟩

/-- The two source single sums can include their otherwise absent endpoint terms. -/
theorem pair_added_endpoint_terms_zero {m : ℕ} (G : Fin (m+2) → Fin (m+2) → ℝ)
    (hs : ∀ i j, G i j = G j i) (hg : ∀ j, G (Fin.last (m+1)) j = 0) :
    G 0 (Fin.last m).castSucc*G (Fin.last m).succ (Fin.last m).succ-
      G 0 (Fin.last m).succ*G (Fin.last m).castSucc (Fin.last m).succ = 0 ∧
    G 0 0*G 0 (1 : Fin (m+2))-G 0 (1 : Fin (m+2))*G 0 0 = 0 := by
  have hc : ∀ i, G i (Fin.last (m+1)) = 0 := fun i => (hs i _).trans (hg i)
  have hlast : (Fin.last m).succ = Fin.last (m+1) := rfl
  constructor
  · simp only [hlast,hg,hc,mul_zero,sub_self]
  · ring

end FiniteAvalanches.Electrical
