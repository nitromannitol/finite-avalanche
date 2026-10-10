import FiniteAvalanches.Electrical.Trees.PairingGroves
import FiniteAvalanches.Electrical.Green.Pendant
import Mathlib.Data.Finset.Sum

/-! Original copied-edge reachability and forests under finite pendant extension. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E K : Type}
noncomputable local instance : DecidableEq (E ⊕ K) := Classical.decEq _

/-- Every original copy is retained, with one new unit copy to each fresh vertex. -/
def withPendants (J : CopiedGraph V E) (z : K → V) : CopiedGraph (V ⊕ K) (E ⊕ K) :=
  ⟨pendantLeft J.left z,pendantRight J.right⟩

theorem pendant_reaches_reverse {W D : Type}
    (J : CopiedGraph W D) {F : Finset D} {x y : W} (h : J.reaches F x y) :
    J.reaches F y x := by
  induction h with
  | refl => exact .refl
  | tail _ h ih =>
    obtain ⟨e,he,hexy⟩ := h
    exact (Relation.ReflTransGen.single ⟨e,he,hexy.elim
      (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)⟩).trans ih

/-- A walk projects to a walk on exactly its selected original copies. -/
theorem pendant_reach_project (J : CopiedGraph V E) (z : K → V)
    {S : Finset (E ⊕ K)} {x y : V ⊕ K}
    (h : (J.withPendants z).reaches S x y) :
    J.reaches S.toLeft (pendantCollapse z x) (pendantCollapse z y) := by
  induction h with
  | refl => exact .refl
  | @tail y w h hw ih =>
    obtain ⟨e,he,hexy⟩ := hw
    rcases e with e | k
    · apply ih.tail
      refine ⟨e,Finset.mem_toLeft.mpr he,?_⟩
      rcases hexy with ⟨ha,hb⟩ | ⟨hb,ha⟩
      · exact Or.inl ⟨congrArg (pendantCollapse z) ha,congrArg (pendantCollapse z) hb⟩
      · exact Or.inr ⟨congrArg (pendantCollapse z) hb,congrArg (pendantCollapse z) ha⟩
    · have hw : pendantCollapse z y = pendantCollapse z w := by
        rcases hexy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
      rw [← hw]
      exact ih

/-- Original walks lift without using any fresh edge. -/
theorem pendant_reach_lift (J : CopiedGraph V E) (z : K → V)
    {S : Finset (E ⊕ K)} {x y : V} (h : J.reaches S.toLeft x y) :
    (J.withPendants z).reaches S (Sum.inl x) (Sum.inl y) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih =>
    obtain ⟨e,he,hexy⟩ := h
    apply ih.tail
    refine ⟨Sum.inl e,Finset.mem_toLeft.mp he,?_⟩
    rcases hexy with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact Or.inl ⟨congrArg Sum.inl ha,congrArg Sum.inl hb⟩
    · exact Or.inr ⟨congrArg Sum.inl hb,congrArg Sum.inl ha⟩

/-- Omitting its unique incident copy isolates the fresh vertex, including length-zero walks. -/
theorem pendant_missing_isolated (J : CopiedGraph V E) (z : K → V)
    {S : Finset (E ⊕ K)} (k : K) (hk : Sum.inr k ∉ S) {y : V ⊕ K}
    (h : (J.withPendants z).reaches S (Sum.inr k) y) : y = Sum.inr k := by
  induction h with
  | refl => rfl
  | @tail y w h hw ih =>
    obtain ⟨e,he,hexy⟩ := hw
    subst y
    rcases e with e | j
    · rcases hexy with ⟨ha,_⟩ | ⟨hb,_⟩
      · exact (Sum.inl_ne_inr (show Sum.inl _ = Sum.inr k from ha)).elim
      · exact (Sum.inl_ne_inr (show Sum.inl _ = Sum.inr k from hb)).elim
    · rcases hexy with ⟨ha,_⟩ | ⟨hb,_⟩
      · exact (Sum.inl_ne_inr (show Sum.inl _ = Sum.inr k from ha)).elim
      · have hj : j = k := Sum.inr.inj hb
        exact (hk (hj ▸ he)).elim

/-- When every pendant copy is present, all reachability is exactly collapsed original reachability. -/
theorem pendant_reach_iff (J : CopiedGraph V E) (z : K → V)
    (S : Finset (E ⊕ K)) (hs : ∀ k, Sum.inr k ∈ S) (x y : V ⊕ K) :
    (J.withPendants z).reaches S x y ↔
      J.reaches S.toLeft (pendantCollapse z x) (pendantCollapse z y) := by
  refine ⟨J.pendant_reach_project z,fun h => ?_⟩
  have link (t : V ⊕ K) : (J.withPendants z).reaches S
      (Sum.inl (pendantCollapse z t)) t := by
    rcases t with t | k
    · exact .refl
    · exact Relation.ReflTransGen.single ⟨Sum.inr k,hs k,Or.inl ⟨rfl,rfl⟩⟩
  exact (pendant_reaches_reverse _ (link x)).trans ((J.pendant_reach_lift z h).trans (link y))

/-- Each original erase projects to erase of that same original identifier. -/
theorem pendant_toLeft_erase (S : Finset (E ⊕ K)) (e : E) :
    (S.erase (Sum.inl e)).toLeft = S.toLeft.erase e := by
  ext f
  simp only [Finset.mem_toLeft,Finset.mem_erase,ne_eq,Sum.inl.injEq]

/-- Adding or removing pendant leaves cannot create or destroy an original copied cycle. -/
theorem pendant_forest_iff (J : CopiedGraph V E) (z : K → V) (S : Finset (E ⊕ K)) :
    (∀ e ∈ S, ¬(J.withPendants z).reaches (S.erase e)
      ((J.withPendants z).left e) ((J.withPendants z).right e)) ↔
    (∀ e ∈ S.toLeft, ¬J.reaches (S.toLeft.erase e) (J.left e) (J.right e)) := by
  constructor
  · intro h e he hr
    apply h (Sum.inl e) (Finset.mem_toLeft.mp he)
    apply J.pendant_reach_lift z
    rw [pendant_toLeft_erase]
    exact hr
  · intro h e he hr
    rcases e with e | k
    · apply h e (Finset.mem_toLeft.mpr he)
      have hp := J.pendant_reach_project z hr
      rw [pendant_toLeft_erase] at hp
      exact hp
    · have hi := J.pendant_missing_isolated z k (by simp)
        (pendant_reaches_reverse _ hr)
      exact Sum.inl_ne_inr hi

variable [Fintype K]

/-- The actual extension of an original subset adds every distinct fresh edge exactly once. -/
def pendantLift (F : Finset E) : Finset (E ⊕ K) := F.disjSum Finset.univ

@[simp] theorem pendantLift_toLeft (F : Finset E) : (pendantLift (K:=K) F).toLeft = F :=
  by simp only [pendantLift,Finset.toLeft_disjSum]

@[simp] theorem pendantLift_mem_fresh (F : Finset E) (k : K) :
    Sum.inr k ∈ pendantLift (K:=K) F := by simp [pendantLift]

/-- A subset containing all pendant copies is recovered from its literal original part. -/
theorem pendantLift_project (S : Finset (E ⊕ K)) (h : ∀ k, Sum.inr k ∈ S) :
    pendantLift (K:=K) S.toLeft = S := by
  have hr : S.toRight = Finset.univ := by
    ext k
    simp only [Finset.mem_toRight,Finset.mem_univ,iff_true]
    exact h k
  rw [pendantLift,← hr,Finset.toLeft_disjSum_toRight]

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
