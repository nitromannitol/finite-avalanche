import FiniteAvalanches.Electrical.Plane.Stream
import FiniteAvalanches.Electrical.ConnectedLevels

/-! Maximum-principle bounds on the actual original voltage and augmented dual stream. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- The normalized original voltage lies between its two terminal values. -/
theorem voltage_range {V E : Type*} [Fintype V] [Fintype E] (a b : E → V)
    (alpha beta : V) (hc : (supportGraph a b).Preconnected) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) (x : V) :
    0 ≤ phi x ∧ phi x ≤ 1 := by
  let B : Finset V := {alpha,beta}
  have hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y :=
    fun x => ⟨alpha,Finset.mem_insert_self _ _,hc x alpha⟩
  have hH : ∀ x, x ∉ B → laplacian a b phi x = 0 := by
    intro x hx
    simp only [B,Finset.mem_insert,Finset.mem_singleton,not_or] at hx
    exact hh x hx.1 hx.2
  have hup := le_of_harmonic a b B hB phi 1 (by
    intro y hy
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with h | h
    · rw [h,hp0]; norm_num
    · rw [h,hp1]) hH x
  have hlo := le_of_harmonic a b B hB ((-1 : ℝ) • phi) 0 (by
    intro y hy
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at hy
    simp only [Pi.smul_apply,smul_eq_mul,neg_one_mul]
    rcases hy with h | h
    · rw [h,hp0,neg_zero]
    · rw [h,hp1]; norm_num) (by
      intro y hy
      rw [laplacian_smul,hH y hy,mul_zero]) x
  simp only [Pi.smul_apply,smul_eq_mul,neg_one_mul] at hlo
  exact ⟨by linarith only [hlo],hup⟩

/-- The positive dual Laplacian of the stream vanishes away from the actual closing-arc faces. -/
theorem stream_dual_harmonic {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (phi : V → ℝ) (M : ℝ) (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (f : ArcFace R da db)
    (hfr : f ≠ arcRightFace R da db (.inr false))
    (hfl : f ≠ arcLeftFace R da db (.inr false)) :
    laplacian (dualA R da db) (dualB R da db) psi f = 0 := by
  have hg : copyGradient (dualA R da db) (dualB R da db) psi = -physicalArcFlow a b phi M := by
    funext e
    have h := hp (arcForward e)
    rw [← arcSignedFlow_physical,arcSignedFlow_forward] at h
    change psi (dualB R da db e)-psi (dualA R da db e) = physicalArcFlow a b phi M e at h
    simp only [copyGradient,Pi.neg_apply]
    linarith only [h]
  have hr : dualA R da db (.inr ()) ≠ f := Ne.symm hfr
  have hl : dualB R da db (.inr ()) ≠ f := Ne.symm hfl
  have hprimal := dualBoundary_primalGradient R alpha beta hne da db ha hb phi f
  have hbnd : copyBoundary (dualA R da db) (dualB R da db) (physicalArcFlow a b phi M) f = 0 := by
    simpa only [copyBoundary,Fintype.sum_sum_type,Fintype.sum_unique,physicalArcFlow,
      copyGradient,arcA,arcB,if_neg hr,if_neg hl,sub_self,add_zero] using hprimal
  rw [← copyBoundary_gradient,hg]
  have hn := congrFun ((boundaryMap (dualA R da db) (dualB R da db)).map_neg (physicalArcFlow a b phi M)) f
  change copyBoundary _ _ (-physicalArcFlow a b phi M) f = -copyBoundary _ _ (physicalArcFlow a b phi M) f at hn
  rw [hn,hbnd,neg_zero]

/-- Dual connectedness and the two actual exterior values bound every face stream. -/
theorem stream_range {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) (f : ArcFace R da db) :
    0 ≤ psi f ∧ psi f ≤ M := by
  let A := arcRightFace R da db (.inr false)
  let B := arcLeftFace R da db (.inr false)
  let bd : Finset (ArcFace R da db) := {A,B}
  have h1 : psi B = M := exterior_stream_values R da db phi psi M (hp (.inr false)) h0
  have hd := dual_preconnected R alpha beta hne da db ha hb hc
  have hbd : ∀ f, ∃ g ∈ bd, (supportGraph (dualA R da db) (dualB R da db)).Reachable f g :=
    fun f => ⟨A,Finset.mem_insert_self _ _,hd f A⟩
  have hh : ∀ f, f ∉ bd → laplacian (dualA R da db) (dualB R da db) psi f = 0 := by
    intro f hf
    simp only [bd,Finset.mem_insert,Finset.mem_singleton,not_or] at hf
    exact stream_dual_harmonic R alpha beta hne da db ha hb phi M psi hp f hf.1 hf.2
  have hup := le_of_harmonic (dualA R da db) (dualB R da db) bd hbd psi M (by
    intro g hg
    simp only [bd,Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with hg | hg
    · rw [hg]; exact h0.trans_le hM
    · rw [hg,h1]) hh f
  have hlo := le_of_harmonic (dualA R da db) (dualB R da db) bd hbd ((-1 : ℝ) • psi) 0 (by
    intro g hg
    simp only [bd,Finset.mem_insert,Finset.mem_singleton] at hg
    simp only [Pi.smul_apply,smul_eq_mul,neg_one_mul]
    rcases hg with hg | hg
    · rw [hg,h0,neg_zero]
    · rw [hg,h1]; exact neg_nonpos.mpr hM) (by
      intro g hg
      rw [laplacian_smul,hh g hg,mul_zero]) f
  simp only [Pi.smul_apply,smul_eq_mul,neg_one_mul] at hlo
  exact ⟨by linarith only [hlo],hup⟩

/-- Both ranges and the canonical strict-level connectivity are consumed from actual voltage data. -/
theorem voltage_range_and_levels {V E : Type*} [Fintype V] [Fintype E] (a b : E → V)
    (alpha beta : V) (hc : (supportGraph a b).Preconnected) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    (∀ x, 0 ≤ phi x ∧ phi x ≤ 1) ∧
    ∀ t : ℝ, 0 < t → t < 1 →
      ((supportGraph a b).induce {x | phi x < t}).Connected ∧
      ((supportGraph a b).induce {x | t < phi x}).Connected := by
  letI : Nonempty V := ⟨alpha⟩
  exact ⟨voltage_range a b alpha beta hc phi hp0 hp1 hh,
    fun t ht0 ht1 => connected_voltage_levels a b ⟨hc⟩ phi alpha beta hh hp0 hp1 t ht0 ht1⟩

end FiniteAvalanches.Electrical.Plane
