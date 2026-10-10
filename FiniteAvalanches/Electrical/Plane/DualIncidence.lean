import FiniteAvalanches.Electrical.Plane.DualGraph
import FiniteAvalanches.Electrical.Plane.Incidence

/-! Literal copied-flow adapters and the signed local primal-star / dual-cycle identities. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

private theorem if_sub_zero (p : Prop) [Decidable p] (u v : ℝ) :
    (if p then u-v else 0) = (if p then u else 0)-(if p then v else 0) := by
  split_ifs <;> simp

/-- Antisymmetric extension of a flow on once-oriented copies. -/
def signedFlow {E : Type*} (j : E → ℝ) (d : Dart E) : ℝ := if d.2 then -j d.1 else j d.1

theorem copyBoundary_eq_dart_sum {V E : Type*} [Fintype E] (a b : E → V)
    (j : E → ℝ) (x : V) :
    copyBoundary a b j x = ∑ d : Dart E, if tail a b d = x then signedFlow j d else 0 := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,tail,signedFlow,Bool.false_eq_true,↓reduceIte]
  unfold copyBoundary
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

def arcSignedFlow {E : Type*} (j : ArcEdge E → ℝ) (d : ArcDart E) : ℝ :=
  signedFlow j ((arcDartEquiv E).symm d)

@[simp] theorem arcSignedFlow_forward {E : Type*} (j : ArcEdge E → ℝ) (e : ArcEdge E) :
    arcSignedFlow j (arcForward e) = j e := by cases e <;> rfl

@[simp] theorem arcSignedFlow_reverse {E : Type*} (j : ArcEdge E → ℝ) (d : ArcDart E) :
    arcSignedFlow j (arcReverse E d) = -arcSignedFlow j d := by
  cases d with
  | inl d => rcases d with ⟨e,c⟩; cases c <;> simp [arcSignedFlow,signedFlow,arcDartEquiv,arcReverse,reverse]
  | inr c => cases c <;> simp [arcSignedFlow,signedFlow,arcDartEquiv,arcReverse]

theorem copyBoundary_eq_arc_sum {V E : Type*} [Fintype E] (a b : E → V)
    (alpha beta : V) (j : ArcEdge E → ℝ) (x : V) :
    copyBoundary (arcA a alpha) (arcB b beta) j x =
      ∑ d : ArcDart E, if arcTail a b alpha beta d = x then arcSignedFlow j d else 0 := by
  rw [copyBoundary_eq_dart_sum]
  apply Fintype.sum_equiv (arcDartEquiv E)
  intro d
  rw [arcTail_equiv]
  simp only [arcSignedFlow,Equiv.symm_apply_apply]

/-- Face increments in the physical primal-current convention, opposite dual voltage gradients. -/
noncomputable def streamMap {V E : Type*} {a b : E → V} (R : EdgeRotation a b) (da db : Dart E) :
    (ArcFace R da db → ℝ) →ₗ[ℝ] (ArcEdge E → ℝ) where
  toFun psi e := psi (dualB R da db e)-psi (dualA R da db e)
  map_add' psi chi := by funext e; simp only [Pi.add_apply]; ring
  map_smul' r psi := by funext e; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

theorem arcSignedFlow_streamMap {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (da db : Dart E) (psi : ArcFace R da db → ℝ) (d : ArcDart E) :
    arcSignedFlow (streamMap R da db psi) d =
      psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) := by
  cases d with
  | inl d => rcases d with ⟨e,c⟩; cases c <;> simp [arcSignedFlow,signedFlow,arcDartEquiv,streamMap,dualA,dualB,arcForward,arcRightFace,arcReverse,reverse]
  | inr c => cases c <;> simp [arcSignedFlow,signedFlow,arcDartEquiv,streamMap,dualA,dualB,arcForward,arcRightFace,arcReverse]

/-- Telescoping around every actual vertex: integrated dual increments have zero primal divergence. -/
theorem copyBoundary_streamMap {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (psi : ArcFace R da db → ℝ) (x : V) :
    copyBoundary (arcA a alpha) (arcB b beta) (streamMap R da db psi) x = 0 := by
  rw [copyBoundary_eq_arc_sum]
  simp only [arcSignedFlow_streamMap,if_sub_zero,Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  have hs := Equiv.sum_comp (insertArcRotation R da db)
    (fun d => if arcTail a b alpha beta d = x then psi (arcLeftFace R da db d) else 0)
  simp only [arcTail_insertArcRotation R alpha beta hne da db ha hb,arcLeftFace_next] at hs
  exact hs.symm

/-- Physical copied flow: original voltage gradients and closing alpha-to-beta current +M. -/
def physicalArcFlow {V E : Type*} (a b : E → V) (phi : V → ℝ) (M : ℝ) : ArcEdge E → ℝ
  | .inl e => phi (a e)-phi (b e)
  | .inr _ => M

theorem arcSignedFlow_physical {V E : Type*} (a b : E → V) (phi : V → ℝ) (M : ℝ) (d : ArcDart E) :
    arcSignedFlow (physicalArcFlow a b phi M) d = arcCurrent a b phi M d := by
  cases d with
  | inl d => rcases d with ⟨e,c⟩; cases c <;> simp [arcSignedFlow,signedFlow,arcDartEquiv,physicalArcFlow,arcCurrent,current,tail,head,reverse]
  | inr c => cases c <;> rfl

theorem copyBoundary_physical {V E : Type*} [Fintype E] (a b : E → V)
    (alpha beta : V) (phi : V → ℝ) (M : ℝ) (x : V) :
    copyBoundary (arcA a alpha) (arcB b beta) (physicalArcFlow a b phi M) x =
      arcDivergence a b alpha beta phi M x := by
  rw [copyBoundary_eq_arc_sum]
  simp only [arcSignedFlow_physical,arcDivergence]

/-- The coefficients of a primal vertex potential form an actual dual cycle. -/
theorem dualBoundary_primalGradient {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (q : V → ℝ) (f : ArcFace R da db) :
    copyBoundary (dualA R da db) (dualB R da db)
      (copyGradient (arcA a alpha) (arcB b beta) q) f = 0 := by
  classical
  letI : DecidableEq (ArcFace R da db) := Classical.decEq _
  rw [copyBoundary_eq_dart_sum]
  have he : ∀ d : Dart (ArcEdge E),
      (if tail (dualA R da db) (dualB R da db) d = f then
        signedFlow (copyGradient (arcA a alpha) (arcB b beta) q) d else 0) =
      (if arcRightFace R da db (arcDartEquiv E d) = f then
        q (arcTail a b alpha beta (arcDartEquiv E d))-
          q (arcTail a b alpha beta (arcReverse E (arcDartEquiv E d))) else 0) := by
    intro d
    rw [(dual_faces_equiv R da db d).1]
    rcases d with ⟨e,c⟩
    cases e <;> cases c <;> simp [signedFlow,copyGradient,arcA,arcB,tail,arcDartEquiv,arcTail,arcReverse,reverse]
  have heq := Finset.sum_congr (s₁ := (Finset.univ : Finset (Dart (ArcEdge E)))) rfl (fun d _ => he d)
  refine heq.trans ?_
  refine (Equiv.sum_comp (arcDartEquiv E) (fun d => if arcRightFace R da db d = f then
    q (arcTail a b alpha beta d)-q (arcTail a b alpha beta (arcReverse E d)) else 0)).trans ?_
  have hr (d : ArcDart E) : arcRightFace R da db (arcReverse E d) = arcLeftFace R da db d := by
    simp only [arcRightFace,arcReverse_arcReverse]
  have hs := Equiv.sum_comp (arcReverse E) (fun d => if arcRightFace R da db d = f then
    q (arcTail a b alpha beta d)-q (arcTail a b alpha beta (arcReverse E d)) else 0)
  rw [← hs]
  simp only [hr,arcReverse_arcReverse,if_sub_zero,Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  have hf (d : ArcDart E) : arcLeftFace R da db (arcFaceNext R da db d) = arcLeftFace R da db d := by
    apply Quotient.sound
    exact (show (arcFaceNext R da db).SameCycle d (arcFaceNext R da db d) from ⟨1,by simp⟩).symm
  have ht (d : ArcDart E) : arcTail a b alpha beta (arcFaceNext R da db d) =
      arcTail a b alpha beta (arcReverse E d) :=
    arcTail_insertArcRotation R alpha beta hne da db ha hb _
  have hs' := Equiv.sum_comp (arcFaceNext R da db)
    (fun d => if arcLeftFace R da db d = f then q (arcTail a b alpha beta d) else 0)
  simp only [hf,ht] at hs'
  exact hs'

end FiniteAvalanches.Electrical.Plane
