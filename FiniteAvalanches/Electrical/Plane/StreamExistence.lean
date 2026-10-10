import FiniteAvalanches.Electrical.Plane.DualIncidence
import FiniteAvalanches.Electrical.Plane.Dimension
import FiniteAvalanches.Electrical.Plane.FaceCardinality

/-! Gauge-fixed stream existence from actual rotation topology and the explicit Euler equation.
A plane embedding's production of these topology premises is a separate theorem. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- Adding the closing arc preserves primal connectedness, including all old copies. -/
theorem arc_primal_preconnected {V E : Type*} (a b : E → V) (alpha beta : V)
    (hc : (supportGraph a b).Preconnected) :
    (supportGraph (arcA a alpha) (arcB b beta)).Preconnected := by
  apply hc.mono
  intro x y h
  obtain ⟨hne,e,he⟩ := h
  exact ⟨hne,.inl e,he⟩

/-- Actual exterior face chosen for the zero gauge. -/
noncomputable def streamBase {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) : ArcFace R da db :=
  arcRightFace R da db (.inr false)

/-- Face coordinates with prescribed zero on the right side of the closing arc. -/
noncomputable def gaugeStreamMap {V E : Type*} {a b : E → V} (R : EdgeRotation a b) (da db : Dart E) :
    ({f : ArcFace R da db // f ≠ streamBase R da db} → ℝ) →ₗ[ℝ] (ArcEdge E → ℝ) :=
  (streamMap R da db).comp (rootExtend (streamBase R da db))

/-- Connectedness of the actual dual makes the gauged face-gradient map injective. -/
theorem gaugeStreamMap_injective {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected) : Function.Injective (gaugeStreamMap R da db) := by
  intro q r h
  apply rootExtend_injective (streamBase R da db)
  let psi := rootExtend (streamBase R da db) q
  let chi := rootExtend (streamBase R da db) r
  let delta := psi-chi
  have hedge (e : ArcEdge E) : delta (dualA R da db e) = delta (dualB R da db e) := by
    have he := congrFun h e
    change psi (dualB R da db e)-psi (dualA R da db e) =
      chi (dualB R da db e)-chi (dualA R da db e) at he
    dsimp [delta]
    linarith only [he]
  have hd := dual_preconnected R alpha beta hne da db ha hb hc
  funext f
  have he := eq_of_reachable (dualA R da db) (dualB R da db) delta hedge (hd f (streamBase R da db))
  have hz : delta (streamBase R da db) = 0 := by
    simp only [delta,Pi.sub_apply,psi,chi,rootExtend_root,sub_self]
  rw [hz] at he
  exact sub_eq_zero.mp he

/-- The actual dual face gradients take values in the kernel of primal incidence. -/
noncomputable def streamCycleMap {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) :
    ({f : ArcFace R da db // f ≠ streamBase R da db} → ℝ) →ₗ[ℝ]
      LinearMap.ker (anchoredBoundary (arcA a alpha) (arcB b beta) alpha) where
  toFun q := ⟨gaugeStreamMap R da db q,by
    funext x
    exact copyBoundary_streamMap R alpha beta hne da db ha hb
      (rootExtend (streamBase R da db) q) x.val⟩
  map_add' q r := Subtype.ext ((gaugeStreamMap R da db).map_add q r)
  map_smul' c q := Subtype.ext ((gaugeStreamMap R da db).map_smul c q)

/-- Euler and the proved common-right-face split give exactly the needed dimension. -/
theorem streamCycleMap_surjective_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected)
    (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2) :
    Function.Surjective (streamCycleMap R alpha beta hne da db ha hb) := by
  letI : DecidableEq (ArcFace R da db) := Classical.decEq _
  have hneD : da ≠ db := by intro h; rw [h,hb] at ha; exact hne ha.symm
  have hf := (arcFace_card_and_distinct R da db hneD hface).1
  have hv : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨alpha⟩
  have hfaces : 0 < Fintype.card (ArcFace R da db) :=
    Fintype.card_pos_iff.mpr ⟨streamBase R da db⟩
  have hd := finrank_ker_anchoredBoundary (arcA a alpha) (arcB b beta) alpha
    (arc_primal_preconnected a b alpha beta hc)
  simp only [Fintype.card_sum,Fintype.card_unit] at hd
  apply surjective_of_injective_of_finrank_eq
  · intro q r h
    exact gaugeStreamMap_injective R alpha beta hne da db ha hb hc (congrArg Subtype.val h)
  · rw [Module.finrank_pi,card_nonroot]
    omega

/-- Existence is proved for every actual balanced copied flow, before any stream is selected. -/
theorem existsUnique_stream_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected)
    (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (j : ArcEdge E → ℝ)
    (hj : ∀ x, copyBoundary (arcA a alpha) (arcB b beta) j x = 0) :
    ∃! psi : ArcFace R da db → ℝ,
      (∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcSignedFlow j d) ∧
      psi (streamBase R da db) = 0 := by
  have hker : j ∈ LinearMap.ker (anchoredBoundary (arcA a alpha) (arcB b beta) alpha) :=
    (anchoredBoundary_eq_zero_iff _ _ alpha j).mpr hj
  obtain ⟨q,hq⟩ := streamCycleMap_surjective_of_euler R alpha beta hne da db ha hb hc hface heuler ⟨j,hker⟩
  have hflow : gaugeStreamMap R da db q = j := congrArg Subtype.val hq
  refine ⟨rootExtend (streamBase R da db) q,⟨?_,rootExtend_root _ q⟩,?_⟩
  · intro d
    rw [← arcSignedFlow_streamMap]
    change arcSignedFlow (gaugeStreamMap R da db q) d = _
    rw [hflow]
  · intro chi hchi
    let r : {f : ArcFace R da db // f ≠ streamBase R da db} → ℝ := fun f => chi f.val
    have hr : rootExtend (streamBase R da db) r = chi := by
      funext f
      by_cases hf : f = streamBase R da db
      · subst f
        rw [rootExtend_root,hchi.2]
      · simp only [rootExtend,LinearMap.coe_mk,AddHom.coe_mk,dif_neg hf,r]
    have hchiFlow : streamMap R da db chi = j := by
      funext e
      have hh := hchi.1 (arcForward e)
      simpa only [arcSignedFlow_forward,streamMap,LinearMap.coe_mk,AddHom.coe_mk,dualA,dualB] using hh
    have he : gaugeStreamMap R da db r = gaugeStreamMap R da db q := by
      change streamMap R da db (rootExtend (streamBase R da db) r) = _
      rw [hr,hchiFlow,hflow]
    have hqr := gaugeStreamMap_injective R alpha beta hne da db ha hb hc he
    rw [← hr,hqr]

end FiniteAvalanches.Electrical.Plane
