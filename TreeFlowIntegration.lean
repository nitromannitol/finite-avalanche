import FiniteAvalanches.Electrical.Trees.TwoCopyGroves
import FiniteAvalanches.Electrical.Plane.Incidence
import FiniteAvalanches.Electrical.Green.Grounded
import Mathlib.Order.Minimal

/-! Kirchhoff integration of copied currents on finite trees. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LovaszStream
open StatementGeometry Plane
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- The incidence pairing holds for arbitrary signed original-copy currents. -/
theorem sum_mul_copyBoundary (a b : E → V) (q : V → ℝ) (j : E → ℝ) :
    (∑ x, q x*copyBoundary a b j x) = ∑ e, (q (a e)-q (b e))*j e := by
  simp only [copyBoundary,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [mul_sub,mul_ite,mul_zero,Finset.sum_sub_distrib,
    Finset.sum_ite_eq,Finset.mem_univ,if_true]
  ring

omit [Fintype V] [Fintype E] in
/-- Copied walks on a subset give supporting-graph walks on its literal ID subtype. -/
theorem support_preconnected_of_copied_reaches (J : CopiedGraph V E) (T : Finset E)
    (hc : ∀ x y, J.reaches T x y) :
    (supportGraph (fun e : T => J.left e.val) (fun e : T => J.right e.val)).Preconnected := by
  intro x y
  induction hc x y with
  | refl => exact .refl _
  | @tail z y _ hzy ih =>
    obtain ⟨e,he,hends⟩ := hzy
    by_cases h : z = y
    · exact h ▸ ih
    · exact ih.trans (SimpleGraph.Adj.reachable ⟨h,⟨e,he⟩,hends⟩)

omit [Fintype V] in
/-- A connected finite copied graph has a minimal connected copy set. -/
theorem exists_spanningTree (J : CopiedGraph V E) (root : V)
    (hc : (supportGraph J.left J.right).Preconnected) : Nonempty J.SpanningTree := by
  have hfull (x y : V) : J.reaches Finset.univ x y := by
    obtain ⟨p⟩ := hc x y
    induction p with
    | nil => exact .refl
    | cons h p ih =>
      obtain ⟨_,e,he⟩ := h
      exact (Relation.ReflTransGen.single ⟨e,Finset.mem_univ _,he⟩).trans ih
  obtain ⟨T,hT,hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun T : Finset E => ∀ x y, J.reaches T x y) ⟨Finset.univ,hfull⟩
  refine ⟨⟨T,⟨⟨root,Set.mem_univ root⟩,hT,?_⟩⟩⟩
  intro e he hepath
  have hconn (x y : V) : J.reaches (T.erase e) x y := by
    induction hT x y with
    | refl => exact .refl
    | @tail z y _ hzy ih =>
      obtain ⟨f,hf,hends⟩ := hzy
      have hstep : J.reaches (T.erase e) z y := by
        by_cases hfe : f = e
        · subst f
          rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact hepath
          · exact CopiedGraph.TwoCopy.reaches_symm J hepath
        · exact .single ⟨f,Finset.mem_erase.mpr ⟨hfe,hf⟩,hends⟩
      exact ih.trans hstep
  have hi : T ⊆ T.erase e := hmin hconn (Finset.erase_subset e T)
  exact Finset.notMem_erase e T (hi he)

/-- A divergence-free copied flow supported on a forest vanishes, by its one-edge cuts. -/
theorem flow_eq_zero_of_forest (J : CopiedGraph V E) (T : Finset E)
    (hforest : ∀ e ∈ T, ¬J.reaches (T.erase e) (J.left e) (J.right e))
    (j : E → ℝ) (hoff : ∀ e, e ∉ T → j e = 0)
    (hb : ∀ x, copyBoundary J.left J.right j x = 0) : j = 0 := by
  funext e
  change j e = 0
  by_cases he : e ∈ T
  · let U : Set V := {x | J.reaches (T.erase e) (J.left e) x}
    let q : V → ℝ := fun x => if x ∈ U then 1 else 0
    have hleft : J.left e ∈ U := Relation.ReflTransGen.refl
    have hright : J.right e ∉ U := hforest e he
    have hedge (f : E) : (q (J.left f)-q (J.right f))*j f = if f = e then j e else 0 := by
      by_cases hfe : f = e
      · subst f
        simp only [q,if_pos hleft,if_neg hright,sub_zero,one_mul,↓reduceIte]
      · rw [if_neg hfe]
        by_cases hf : f ∈ T
        · have hfer : f ∈ T.erase e := Finset.mem_erase.mpr ⟨hfe,hf⟩
          have hu : J.left f ∈ U ↔ J.right f ∈ U := by
            constructor
            · intro h
              exact h.trans (.single ⟨f,hfer,Or.inl ⟨rfl,rfl⟩⟩)
            · intro h
              exact h.trans (.single ⟨f,hfer,Or.inr ⟨rfl,rfl⟩⟩)
          simp only [q,hu,sub_self,zero_mul]
        · rw [hoff f hf,mul_zero]
    have hs := sum_mul_copyBoundary J.left J.right q j
    simp only [hb,mul_zero,Finset.sum_const_zero] at hs
    rw [Finset.sum_congr rfl (fun f _ => hedge f)] at hs
    simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using hs.symm
  · exact hoff e he

/-- Literal zero extension of a current on a selected copy set. -/
def extendCopies (T : Finset E) (j : T → ℝ) (e : E) : ℝ :=
  if he : e ∈ T then j ⟨e,he⟩ else 0

omit [Fintype V] in
/-- Restricting current support changes the sum's index, not its incidence or sign. -/
theorem copyBoundary_extend (J : CopiedGraph V E) (T : Finset E) (j : T → ℝ) (x : V) :
    copyBoundary J.left J.right (extendCopies T j) x =
      copyBoundary (fun e : T => J.left e.val) (fun e : T => J.right e.val) j x := by
  let f : E → ℝ := fun e =>
    (if J.left e = x then extendCopies T j e else 0)-
    (if J.right e = x then extendCopies T j e else 0)
  have hs : (∑ e ∈ T, f e) = ∑ e, f e := by
    apply Finset.sum_subset (Finset.subset_univ T)
    intro e _ he
    simp only [f,extendCopies,dif_neg he,ite_self,sub_self]
  change (∑ e, f e) = _
  rw [← hs,Finset.sum_subtype T (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro e _
  simp only [f,extendCopies,dif_pos e.property]

/-- Every prescribed tree current integrates uniquely once its root potential is fixed. -/
theorem existsUnique_tree_gradient (J : CopiedGraph V E) (T : J.SpanningTree)
    (root : V) (j : T.val → ℝ) :
    ∃! q : V → ℝ, q root = 0 ∧ ∀ e : T.val, q (J.left e.val)-q (J.right e.val) = j e := by
  let a : T.val → V := fun e => J.left e.val
  let b : T.val → V := fun e => J.right e.val
  have hc : (supportGraph a b).Preconnected :=
    support_preconnected_of_copied_reaches J T.val T.property.2.1
  obtain ⟨q,hq,_⟩ := existsUnique_grounded_poisson a b root hc (copyBoundary a b j)
  let r : T.val → ℝ := fun e => (q (a e)-q (b e))-j e
  have hr (x : V) (hx : x ≠ root) : copyBoundary a b r x = 0 := by
    have hlin := congrFun ((boundaryMap a b).map_sub (copyGradient a b q) j) x
    change copyBoundary a b r x = copyBoundary a b (copyGradient a b q) x-copyBoundary a b j x at hlin
    rw [hlin,copyBoundary_gradient,hq.2 x hx,sub_self]
  have hall : ∀ x, copyBoundary a b r x = 0 := by
    apply (anchoredBoundary_eq_zero_iff a b root r).mp
    funext x
    exact hr x.val x.property
  have hext : extendCopies T.val r = 0 := flow_eq_zero_of_forest J T.val T.property.2.2
    (extendCopies T.val r) (fun e he => dif_neg he) (fun x => by rw [copyBoundary_extend]; exact hall x)
  refine ⟨q,⟨hq.1,?_⟩,?_⟩
  · intro e
    have h := congrFun hext e.val
    have hr0 : r e = 0 := by simpa only [extendCopies,dif_pos e.property,Pi.zero_apply] using h
    exact sub_eq_zero.mp hr0
  · intro chi hchi
    have hedge (e : T.val) : (chi-q) (a e) = (chi-q) (b e) := by
      have h1 := hchi.2 e
      have h2 := congrFun hext e.val
      have hqj : q (a e)-q (b e) = j e := by
        apply sub_eq_zero.mp
        simpa only [extendCopies,dif_pos e.property,Pi.zero_apply] using h2
      simp only [Pi.sub_apply]
      linarith only [h1,hqj]
    funext x
    have h := eq_of_reachable a b (chi-q) hedge (hc x root)
    simp only [Pi.sub_apply,hchi.1,hq.1,sub_self] at h
    exact sub_eq_zero.mp h

end
end FiniteAvalanches.Electrical.LovaszStream

#print axioms FiniteAvalanches.Electrical.LovaszStream.exists_spanningTree
#print axioms FiniteAvalanches.Electrical.LovaszStream.flow_eq_zero_of_forest
#print axioms FiniteAvalanches.Electrical.LovaszStream.existsUnique_tree_gradient
