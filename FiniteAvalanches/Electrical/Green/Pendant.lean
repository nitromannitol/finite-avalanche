import FiniteAvalanches.Electrical.Green.Grounded

/-! Unit pendant copies preserve the actual grounded Green kernel off their new diagonals. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical
open scoped BigOperators Classical
noncomputable section
variable {V E K : Type*} [Fintype V] [Fintype E] [Fintype K]

/-- The original copies are included unchanged; each new copy has one original endpoint. -/
def pendantLeft (a : E → V) (z : K → V) : E ⊕ K → V ⊕ K
  | Sum.inl e => Sum.inl (a e)
  | Sum.inr k => Sum.inl (z k)

def pendantRight (b : E → V) : E ⊕ K → V ⊕ K
  | Sum.inl e => Sum.inl (b e)
  | Sum.inr k => Sum.inr k

def pendantCollapse (z : K → V) : V ⊕ K → V := Sum.elim id z

omit [Fintype V] [Fintype E] [Fintype K] in
theorem pendant_preconnected (a b : E → V) (z : K → V)
    (hc : (supportGraph a b).Preconnected) :
    (supportGraph (pendantLeft a z) (pendantRight b)).Preconnected := by
  let hom : supportGraph a b →g supportGraph (pendantLeft a z) (pendantRight b) :=
    ⟨Sum.inl,by
      intro x y h
      obtain ⟨hne,e,he⟩ := h
      refine ⟨fun h => hne (Sum.inl.inj h),Sum.inl e,?_⟩
      rcases he with ⟨ha,hb⟩ | ⟨hb,ha⟩
      · exact Or.inl ⟨congrArg Sum.inl ha,congrArg Sum.inl hb⟩
      · exact Or.inr ⟨congrArg Sum.inl hb,congrArg Sum.inl ha⟩⟩
  have leaf (k : K) : (supportGraph (pendantLeft a z) (pendantRight b)).Reachable
      (Sum.inl (z k)) (Sum.inr k) :=
    SimpleGraph.Adj.reachable ⟨Sum.inl_ne_inr,Sum.inr k,Or.inl ⟨rfl,rfl⟩⟩
  intro x y
  rcases x with x | i <;> rcases y with y | j
  · exact (hc x y).map hom
  · exact ((hc x (z j)).map hom).trans (leaf j)
  · exact (leaf i).symm.trans ((hc (z i) y).map hom)
  · exact ((leaf i).symm.trans ((hc (z i) (z j)).map hom)).trans (leaf j)

omit [Fintype V] in
theorem pendant_laplacian_old (a b : E → V) (z : K → V)
    (f : V ⊕ K → ℝ) (y : V) :
    laplacian (pendantLeft a z) (pendantRight b) f (Sum.inl y) =
      laplacian a b (fun x => f (Sum.inl x)) y +
        ∑ k, if z k = y then f (Sum.inl y)-f (Sum.inr k) else 0 := by
  simp only [laplacian,Fintype.sum_sum_type,pendantLeft,pendantRight,
    Sum.inl.injEq,Sum.inr_ne_inl,if_false,add_zero]

omit [Fintype V] in
theorem pendant_laplacian_leaf (a b : E → V) (z : K → V)
    (f : V ⊕ K → ℝ) (k : K) :
    laplacian (pendantLeft a z) (pendantRight b) f (Sum.inr k) =
      f (Sum.inr k)-f (Sum.inl (z k)) := by
  simp only [laplacian,Fintype.sum_sum_type,pendantLeft,pendantRight,
    Sum.inl_ne_inr,Sum.inr.injEq,if_false,zero_add,add_zero,Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]

/-- The actual unit-injection voltage extends constantly across every new pendant edge. -/
theorem groundedGreen_pendant_old_source (a b : E → V) (z : K → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (x : V) :
    groundedGreen (pendantLeft a z) (pendantRight b) (Sum.inl v)
      (pendant_preconnected a b z hc) (Sum.inl x) =
      fun y => groundedGreen a b v hc x (pendantCollapse z y) := by
  apply (groundedPoisson_eq (pendantLeft a z) (pendantRight b) (Sum.inl v)
    (pendant_preconnected a b z hc) _ _ ?_).symm
  refine ⟨groundedGreen_ground a b v hc x,?_⟩
  intro y hy
  rcases y with y | k
  · rw [pendant_laplacian_old]
    have hz : (∑ k, if z k = y then
        groundedGreen a b v hc x y-groundedGreen a b v hc x (z k) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · rw [h,sub_self]
      · rfl
    change laplacian a b (groundedGreen a b v hc x) y + _ = _
    dsimp only [pendantCollapse,Sum.elim_inl,Sum.elim_inr,id_eq]
    rw [hz,add_zero,groundedGreen_laplacian a b v hc x y
      (fun h => hy (congrArg Sum.inl h))]
    simp only [Sum.inl.injEq]
  · rw [pendant_laplacian_leaf]
    simp only [pendantCollapse,Sum.elim_inr,Sum.elim_inl,id_eq,sub_self,Sum.inr_ne_inl,if_false]

theorem groundedGreen_pendant_leaf_old (a b : E → V) (z : K → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (k : K) (y : V) :
    groundedGreen (pendantLeft a z) (pendantRight b) (Sum.inl v)
      (pendant_preconnected a b z hc) (Sum.inr k) (Sum.inl y) =
      groundedGreen a b v hc (z k) y := by
  rw [groundedGreen_symm,groundedGreen_pendant_old_source]
  exact groundedGreen_symm a b v hc y (z k)

theorem groundedGreen_pendant_old_old (a b : E → V) (z : K → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (x y : V) :
    groundedGreen (pendantLeft a z) (pendantRight b) (Sum.inl v)
      (pendant_preconnected a b z hc) (Sum.inl x) (Sum.inl y) = groundedGreen a b v hc x y :=
  congrFun (groundedGreen_pendant_old_source a b z v hc x) (Sum.inl y)

theorem groundedGreen_pendant_old_leaf (a b : E → V) (z : K → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (x : V) (k : K) :
    groundedGreen (pendantLeft a z) (pendantRight b) (Sum.inl v)
      (pendant_preconnected a b z hc) (Sum.inl x) (Sum.inr k) = groundedGreen a b v hc x (z k) :=
  congrFun (groundedGreen_pendant_old_source a b z v hc x) (Sum.inr k)

/-- Only the fresh vertex's diagonal receives its unit pendant resistance. -/
theorem groundedGreen_pendant_leaf_leaf (a b : E → V) (z : K → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (i j : K) :
    groundedGreen (pendantLeft a z) (pendantRight b) (Sum.inl v)
      (pendant_preconnected a b z hc) (Sum.inr i) (Sum.inr j) =
      groundedGreen a b v hc (z i) (z j) + if j = i then 1 else 0 := by
  have h := groundedGreen_laplacian (pendantLeft a z) (pendantRight b) (Sum.inl v)
    (pendant_preconnected a b z hc) (Sum.inr i) (Sum.inr j) Sum.inr_ne_inl
  rw [pendant_laplacian_leaf a b z,
    groundedGreen_pendant_leaf_old a b z v hc i (z j)] at h
  simp only [Sum.inr.injEq] at h
  linarith only [h]

/-- Fresh copies replace exactly the three terminals that may coincide in the source. -/
def pendantSixAttachments (x : Fin 6 → V) : Fin 3 → V := ![x 2,x 4,x 5]

def pendantSixTerminals (x : Fin 6 → V) : Fin 6 → V ⊕ Fin 3 :=
  ![Sum.inl (x 0),Sum.inl (x 1),Sum.inr 0,Sum.inl (x 3),Sum.inr 1,Sum.inr 2]

/-- The literal four Green products survive all simultaneous endpoint coincidences.
The old ground is retained; no new-copy diagonal is used. -/
theorem groundedGreen_pendant_six_pair_expansion (a b : E → V)
    (hc : (supportGraph a b).Preconnected) (x : Fin 6 → V) :
    let z := pendantSixAttachments x
    let y := pendantSixTerminals x
    let G := fun i j => groundedGreen a b (x 0) hc (x i) (x j)
    let H := fun i j => groundedGreen (pendantLeft a z) (pendantRight b) (Sum.inl (x 0))
      (pendant_preconnected a b z hc) (y i) (y j)
    H 1 2*(H 3 4-H 3 5)-H 1 3*(H 2 4-H 2 5)-
      H 1 4*(H 2 5-H 3 5)+H 1 5*(H 2 4-H 3 4) =
    G 1 2*(G 3 4-G 3 5)-G 1 3*(G 2 4-G 2 5)-
      G 1 4*(G 2 5-G 3 5)+G 1 5*(G 2 4-G 3 4) := by
  intro z y G H
  have h12 : H 1 2 = G 1 2 := groundedGreen_pendant_old_leaf a b z (x 0) hc (x 1) 0
  have h13 : H 1 3 = G 1 3 := groundedGreen_pendant_old_old a b z (x 0) hc (x 1) (x 3)
  have h14 : H 1 4 = G 1 4 := groundedGreen_pendant_old_leaf a b z (x 0) hc (x 1) 1
  have h15 : H 1 5 = G 1 5 := groundedGreen_pendant_old_leaf a b z (x 0) hc (x 1) 2
  have h34 : H 3 4 = G 3 4 := groundedGreen_pendant_old_leaf a b z (x 0) hc (x 3) 1
  have h35 : H 3 5 = G 3 5 := groundedGreen_pendant_old_leaf a b z (x 0) hc (x 3) 2
  have h24 : H 2 4 = G 2 4 := by
    have h := groundedGreen_pendant_leaf_leaf a b z (x 0) hc 0 1
    rw [if_neg (show (1 : Fin 3) ≠ 0 by decide),add_zero] at h
    exact h
  have h25 : H 2 5 = G 2 5 := by
    have h := groundedGreen_pendant_leaf_leaf a b z (x 0) hc 0 2
    rw [if_neg (show (2 : Fin 3) ≠ 0 by decide),add_zero] at h
    exact h
  rw [h12,h13,h14,h15,h34,h35,h24,h25]

end
end FiniteAvalanches.Electrical

set_option pp.fullNames true
#check @FiniteAvalanches.Electrical.groundedGreen_pendant_old_source
#check @FiniteAvalanches.Electrical.groundedGreen_pendant_leaf_old
#check @FiniteAvalanches.Electrical.groundedGreen_pendant_leaf_leaf
#print axioms FiniteAvalanches.Electrical.groundedGreen_pendant_old_source
#print axioms FiniteAvalanches.Electrical.groundedGreen_pendant_leaf_old
#print axioms FiniteAvalanches.Electrical.groundedGreen_pendant_leaf_leaf
#check @FiniteAvalanches.Electrical.groundedGreen_pendant_six_pair_expansion
#print axioms FiniteAvalanches.Electrical.groundedGreen_pendant_six_pair_expansion
