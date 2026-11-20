import FiniteAvalanches.Support.Plane.OuterRedrawing.BaseRealize
import FiniteAvalanches.Support.Plane.OuterRedrawing.SquareCombine
import FiniteAvalanches.Support.Plane.OuterRedrawing.SquareInsert

/-!
# Square realization of every stretch selection

Every selection of a straight drawing containing a stretch of the path, with the
ends of its edges selected, has a square realization. The proof is by strong
induction on the number of selected edges. If no interior vertex of the stretch
carries a selected loop or separates the selection, the stretch is attached from
one side. Otherwise, at such a vertex `v`, let `L` be the set of vertices joined
to the previous path vertex by selected edges avoiding `v`. If `L` contains the
next path vertex, the edges meeting `L` form a smaller selection containing the
stretch, and the remaining edges form a part attached at `v` alone, inserted into
the cusp at `v`. Otherwise the edges meeting `L` and the edges meeting the set
joined to the next path vertex form two smaller selections containing the two
halves of the stretch; they are combined side by side, and the remaining part
attached at `v` is inserted into the cusp at `v`.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set
open scoped Classical

noncomputable section

variable {V E : Type} {J : CopiedGraph V E}

theorem reaches_cases {A : Finset E} {x y : V} (h : J.reaches A x y) :
    x = y ∨ ∃ e ∈ A, J.left e = x ∨ J.right e = x := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, ⟨e, he, hx⟩, -⟩
  · exact Or.inl h
  · right
    refine ⟨e, he, ?_⟩
    rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1

theorem reaches_edge {A : Finset E} {e : E} (he : e ∈ A) :
    J.reaches A (J.left e) (J.right e) :=
  Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

theorem reaches_edge' {A : Finset E} {e : E} (he : e ∈ A) :
    J.reaches A (J.right e) (J.left e) :=
  Relation.ReflTransGen.single ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩

/-- The vertices joined to `w` by selected edges avoiding `v`. -/
def reachSet (J : CopiedGraph V E) (T : Finset E) (v w : V) : Set V :=
  {x | J.reaches (avoiding J T v) x w}

theorem mem_reachSet_self (T : Finset E) (v w : V) : w ∈ reachSet J T v w :=
  Relation.ReflTransGen.refl

theorem ne_of_mem_reachSet {T : Finset E} {v w x : V} (hw : w ≠ v)
    (hx : x ∈ reachSet J T v w) : x ≠ v := by
  rcases reaches_cases hx with rfl | ⟨e, he, hl | hr⟩
  · exact hw
  · rw [← hl]
    exact (Finset.mem_filter.mp he).2.1
  · rw [← hr]
    exact (Finset.mem_filter.mp he).2.2

theorem reachSet_subset {S : Set V} {T : Finset E} {v w : V} (hwS : w ∈ S)
    (hTS : ∀ e ∈ T, J.left e ∈ S ∧ J.right e ∈ S) : reachSet J T v w ⊆ S := by
  intro x hx
  rcases reaches_cases hx with rfl | ⟨e, he, hl | hr⟩
  · exact hwS
  · rw [← hl]
    exact (hTS e (Finset.mem_filter.mp he).1).1
  · rw [← hr]
    exact (hTS e (Finset.mem_filter.mp he).1).2

/-- An edge meeting the set joined to `w` avoiding `v` has its ends in that set or at `v`. -/
theorem reachSet_closed {T : Finset E} {v w : V} (hw : w ≠ v) {e : E} (he : e ∈ T)
    (hx : J.left e ∈ reachSet J T v w ∨ J.right e ∈ reachSet J T v w) :
    (J.left e = v ∨ J.left e ∈ reachSet J T v w) ∧
      (J.right e = v ∨ J.right e ∈ reachSet J T v w) := by
  by_cases hl : J.left e = v
  · refine ⟨Or.inl hl, ?_⟩
    rcases hx with hx | hx
    · exact absurd hl (ne_of_mem_reachSet hw hx)
    · exact Or.inr hx
  by_cases hr : J.right e = v
  · refine ⟨?_, Or.inl hr⟩
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact absurd hr (ne_of_mem_reachSet hw hx)
  have hA : e ∈ avoiding J T v := Finset.mem_filter.mpr ⟨he, hl, hr⟩
  rcases hx with hx | hx
  · exact ⟨Or.inr hx, Or.inr ((reaches_edge' hA).trans hx)⟩
  · exact ⟨Or.inr ((reaches_edge hA).trans hx), Or.inr hx⟩

theorem reachSet_symm {T : Finset E} {v w w' x : V} (hx : x ∈ reachSet J T v w)
    (hx' : x ∈ reachSet J T v w') : w ∈ reachSet J T v w' :=
  (reaches_symm' hx).trans hx'

section PathReach

variable {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

theorem reaches_along_path
    (hends : ∀ i, (J.left (copies i) = path i.castSucc ∧ J.right (copies i) = path i.succ) ∨
      (J.right (copies i) = path i.castSucc ∧ J.left (copies i) = path i.succ))
    {A : Finset E} {r : ℕ} (hrm : r ≤ m) :
    ∀ s : ℕ, r ≤ s → ∀ (hsm : s ≤ m),
      (∀ j : Fin m, r ≤ (j : ℕ) → (j : ℕ) < s → copies j ∈ A) →
      J.reaches A (path ⟨r, by omega⟩) (path ⟨s, by omega⟩) := by
  intro s
  induction s with
  | zero =>
    intro hrs _ _
    have : r = 0 := by omega
    subst this
    exact Relation.ReflTransGen.refl
  | succ s ih =>
    intro hrs hsm hA
    rcases eq_or_lt_of_le hrs with hr | hr
    · subst hr
      exact Relation.ReflTransGen.refl
    · have h1 := ih (by omega) (by omega) fun j hj1 hj2 => hA j hj1 (by omega)
      refine h1.tail ⟨copies ⟨s, by omega⟩, hA _ (by simp; omega) (by simp), ?_⟩
      rcases hends ⟨s, by omega⟩ with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · left
        rw [hl, hr]
        exact ⟨rfl, rfl⟩
      · right
        rw [hl, hr]
        exact ⟨rfl, rfl⟩

theorem copies_mem_avoiding
    (hends : ∀ i, (J.left (copies i) = path i.castSucc ∧ J.right (copies i) = path i.succ) ∨
      (J.right (copies i) = path i.castSucc ∧ J.left (copies i) = path i.succ))
    (hinj : Function.Injective path) {T : Finset E} {j : Fin m} (hj : copies j ∈ T)
    {a : Fin (m + 1)} (h1 : (j : ℕ) ≠ a) (h2 : (j : ℕ) + 1 ≠ a) :
    copies j ∈ avoiding J T (path a) := by
  have hc : path j.castSucc ≠ path a := fun h => h1 (congrArg Fin.val (hinj h))
  have hs : path j.succ ≠ path a := fun h => h2 (congrArg Fin.val (hinj h))
  refine Finset.mem_filter.mpr ⟨hj, ?_, ?_⟩ <;>
    rcases hends j with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · rw [hl]; exact hc
  · rw [hl]; exact hs
  · rw [hr]; exact hs
  · rw [hr]; exact hc

/-- A path edge has one end at each of its two path vertices. -/
theorem copies_end_left
    (hends : ∀ i, (J.left (copies i) = path i.castSucc ∧ J.right (copies i) = path i.succ) ∨
      (J.right (copies i) = path i.castSucc ∧ J.left (copies i) = path i.succ))
    (j : Fin m) {X : Set V} (hX : path j.castSucc ∈ X) :
    J.left (copies j) ∈ X ∨ J.right (copies j) ∈ X := by
  rcases hends j with ⟨hl, -⟩ | ⟨hr, -⟩
  · left
    rwa [hl]
  · right
    rwa [hr]

theorem copies_end_right
    (hends : ∀ i, (J.left (copies i) = path i.castSucc ∧ J.right (copies i) = path i.succ) ∨
      (J.right (copies i) = path i.castSucc ∧ J.left (copies i) = path i.succ))
    (j : Fin m) {X : Set V} (hX : path j.succ ∈ X) :
    J.left (copies j) ∈ X ∨ J.right (copies j) ∈ X := by
  rcases hends j with ⟨-, hr⟩ | ⟨-, hl⟩
  · right
    rwa [hr]
  · left
    rwa [hl]

end PathReach

section Main

variable [Fintype V] [Fintype E] {D : Drawing J} {m : ℕ} {path : Fin (m + 1) → V}
  {copies : Fin m → E}

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

/-- Every stretch selection of a straight drawing whose path lies on the boundary
of the unbounded face has a square realization. -/
theorem exists_squareRealization {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U) :
    ∀ (n : ℕ) (S : Set V) (T : Finset E), T.card = n → ∀ {p q : ℕ}, p < q → q ≤ m →
      (∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → path i ∈ S) →
      (∀ i : Fin m, p ≤ (i : ℕ) → (i : ℕ) < q → copies i ∈ T) →
      (∀ e ∈ T, J.left e ∈ S ∧ J.right e ∈ S) →
      Nonempty (SquareRealization J S T path copies p q) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S T hn p q hpq hqm hpS hcT hTS
  by_cases hbad : ∃ a : ℕ, ∃ hpa : p < a, ∃ haq : a < q,
      (∃ e ∈ T, J.left e = path ⟨a, by omega⟩ ∧ J.right e = path ⟨a, by omega⟩) ∨
      ∃ e ∈ T, ∃ x, (x = J.left e ∨ x = J.right e) ∧ x ≠ path ⟨a, by omega⟩ ∧
        ¬ J.reaches (avoiding J T (path ⟨a, by omega⟩)) x (path ⟨a - 1, by omega⟩)
  swap
  · refine h.exists_squareRealization_base hU hfront S T hpq hqm hcT ?_ ?_
    · intro a hpa haq e he hl
      exact hbad ⟨a, hpa, haq, Or.inl ⟨e, he, hl⟩⟩
    · intro a hpa haq e he x hx hxa
      by_contra hr
      exact hbad ⟨a, hpa, haq, Or.inr ⟨e, he, x, hx, hxa, hr⟩⟩
  obtain ⟨a, hpa, haq, hbad_a⟩ := hbad
  obtain ⟨va, hva⟩ : ∃ v, v = path ⟨a, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨vl, hvl⟩ : ∃ v, v = path ⟨a - 1, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨vr, hvr⟩ : ∃ v, v = path ⟨a + 1, by omega⟩ := ⟨_, rfl⟩
  rw [← hva, ← hvl] at hbad_a
  have hvl_ne : vl ≠ va := by
    rw [hva, hvl]
    intro he
    have := congrArg Fin.val (h.injective he)
    simp only at this
    omega
  have hvr_ne : vr ≠ va := by
    rw [hva, hvr]
    intro he
    have := congrArg Fin.val (h.injective he)
    simp only at this
    omega
  have hvaS : va ∈ S := hva ▸ hpS _ (by show p ≤ a; omega) (by show a ≤ q; omega)
  have hvlS : vl ∈ S := hvl ▸ hpS _ (by show p ≤ a - 1; omega) (by show a - 1 ≤ q; omega)
  have havoid : ∀ j : Fin m, p ≤ (j : ℕ) → (j : ℕ) < q → (j : ℕ) ≠ a → (j : ℕ) + 1 ≠ a →
      copies j ∈ avoiding J T va := by
    intro j hj1 hj2 hj3 hj4
    rw [hva]
    exact copies_mem_avoiding h.ends h.injective (hcT j hj1 hj2) (a := ⟨a, by omega⟩) hj3 hj4
  have hleft : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) < a → path i ∈ reachSet J T va vl := by
    intro i hi1 hi2
    have := reaches_along_path h.ends (A := avoiding J T va) (r := i) (by omega) (a - 1)
      (by omega) (by omega) fun j hj1 hj2 => havoid j (by omega) (by omega) (by omega) (by omega)
    rw [← hvl] at this
    exact this
  have hright : ∀ i : Fin (m + 1), a < (i : ℕ) → (i : ℕ) ≤ q →
      J.reaches (avoiding J T va) (path i) vr := by
    intro i hi1 hi2
    have := reaches_along_path h.ends (A := avoiding J T va) (r := a + 1) (by omega) i
      (by omega) (by omega) fun j hj1 hj2 => havoid j (by omega) (by omega) (by omega) (by omega)
    rw [← hvr] at this
    exact reaches_symm' this
  have hpath_a : ∀ i : Fin (m + 1), (i : ℕ) = a → path i = va := by
    intro i hi
    rw [hva]
    exact congrArg path (Fin.ext hi)
  have hYTS : ∀ (X : Set V) (TY : Finset E), (∀ e ∈ TY, e ∈ T ∧ J.left e ∉ X ∧ J.right e ∉ X) →
      ∀ e ∈ (TY : Set E), J.left e ∈ S \ X ∧ J.right e ∈ S \ X := by
    intro X TY hTY e he
    obtain ⟨heT, h1, h2⟩ := hTY e he
    exact ⟨⟨(hTS e heT).1, h1⟩, ⟨(hTS e heT).2, h2⟩⟩
  have hpend : ∀ (Y : Set V) (TY : Finset E),
      Nonempty (SquareRealization J Y TY path copies a (a + 1)) := fun Y TY =>
    h.exists_squareRealization_of_endsBelow Y TY (Nat.lt_succ_self a) (by omega)
      fun _ _ _ a' h1 h2 => absurd h2 (by omega)
  by_cases hvrL : vr ∈ reachSet J T va vl
  · -- the two sides of the vertex are joined: a part attached at the vertex alone
    set L := reachSet J T va vl with hL
    let TM := T.filter fun e => J.left e ∈ L ∨ J.right e ∈ L
    let TY := T.filter fun e => ¬ (J.left e ∈ L ∨ J.right e ∈ L)
    have hTY_ex : ∃ e ∈ T, ¬ (J.left e ∈ L ∨ J.right e ∈ L) := by
      rcases hbad_a with ⟨e, he, hl, hr⟩ | ⟨e, he, x, hx, hxa, hnr⟩
      · refine ⟨e, he, ?_⟩
        rintro (h1 | h1)
        · exact ne_of_mem_reachSet hvl_ne h1 hl
        · exact ne_of_mem_reachSet hvl_ne h1 hr
      · refine ⟨e, he, fun hmem => ?_⟩
        have hcl := reachSet_closed hvl_ne he hmem
        rcases hx with rfl | rfl
        · rcases hcl.1 with h1 | h1
          · exact hxa h1
          · exact hnr h1
        · rcases hcl.2 with h1 | h1
          · exact hxa h1
          · exact hnr h1
    have hcard : TM.card < n := hn ▸ Finset.card_lt_card (Finset.filter_ssubset.mpr hTY_ex)
    have hpSM : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → path i ∈ insert va L := by
      intro i hi1 hi2
      rcases lt_trichotomy (i : ℕ) a with hia | hia | hia
      · exact mem_insert_of_mem _ (hleft i hi1 hia)
      · rw [hpath_a i hia]
        exact mem_insert _ _
      · exact mem_insert_of_mem _ ((hright i hia hi2).trans hvrL)
    have hcTM : ∀ i : Fin m, p ≤ (i : ℕ) → (i : ℕ) < q → copies i ∈ TM := by
      intro i hi1 hi2
      refine Finset.mem_filter.mpr ⟨hcT i hi1 hi2, ?_⟩
      by_cases hia : (i : ℕ) < a
      · exact copies_end_left h.ends i (hleft _ hi1 hia)
      · exact copies_end_right h.ends i ((hright i.succ (by simp; omega) (by simp; omega)).trans
          hvrL)
    have hTSM : ∀ e ∈ TM, J.left e ∈ insert va L ∧ J.right e ∈ insert va L := by
      intro e he
      obtain ⟨heT, hmem⟩ := Finset.mem_filter.mp he
      obtain ⟨h1, h2⟩ := reachSet_closed hvl_ne heT hmem
      exact ⟨h1, h2⟩
    obtain ⟨M⟩ := ih _ hcard (insert va L) TM rfl hpq hqm hpSM hcTM hTSM
    obtain ⟨Pd⟩ := hpend (S \ L) TY
    have hTSY := hYTS L TY fun e he => by
      obtain ⟨heT, hmem⟩ := Finset.mem_filter.mp he
      exact ⟨heT, fun h1 => hmem (Or.inl h1), fun h1 => hmem (Or.inr h1)⟩
    have hres := SquareRealization.insert hpa.le haq hqm M Pd subset_rfl subset_rfl
      (fun e he => hTSM e he) hTSY
      (by
        intro v hv1 hv2
        rw [← hva]
        rcases hv1 with hv1 | hv1
        · exact hv1
        · exact absurd hv1 hv2.2)
      (by rw [← hva]; exact mem_insert _ _)
      (by rw [← hva]; exact ⟨hvaS, fun h1 => ne_of_mem_reachSet hvl_ne h1 rfl⟩) hpSM hcTM
    have hSe : insert va L ∪ S \ L = S := by
      ext x
      constructor
      · rintro ((rfl | hx) | ⟨hx, -⟩)
        · exact hvaS
        · exact reachSet_subset hvlS hTS hx
        · exact hx
      · intro hx
        by_cases hxL : x ∈ L
        · exact Or.inl (mem_insert_of_mem _ hxL)
        · exact Or.inr ⟨hx, hxL⟩
    have hTe : ((TM : Set E) ∪ (TY : Set E)) = (T : Set E) := by
      ext e
      simp only [TM, TY, Finset.coe_filter, mem_union, mem_setOf_eq]
      tauto
    rw [hSe, hTe] at hres
    exact hres
  · -- the vertex separates: split into a left part, a right part and a pendant part
    set L := reachSet J T va vl with hL
    set R := reachSet J T va vr with hR
    have hLR : ∀ x ∈ L, x ∉ R := fun x hxL hxR => hvrL (reachSet_symm hxR hxL)
    have hvaL : va ∉ L := fun h1 => ne_of_mem_reachSet hvl_ne h1 rfl
    have hvaR : va ∉ R := fun h1 => ne_of_mem_reachSet hvr_ne h1 rfl
    have hvlL : vl ∈ L := mem_reachSet_self T va vl
    have hvrR : vr ∈ R := mem_reachSet_self T va vr
    have hvrS : vr ∈ S := hvr ▸ hpS _ (by show p ≤ a + 1; omega) (by show a + 1 ≤ q; omega)
    let TL := T.filter fun e => J.left e ∈ L ∨ J.right e ∈ L
    let TR := T.filter fun e => J.left e ∈ R ∨ J.right e ∈ R
    let TY := T.filter fun e => ¬ (J.left e ∈ L ∨ J.right e ∈ L) ∧ ¬ (J.left e ∈ R ∨ J.right e ∈ R)
    have hca : copies ⟨a, by omega⟩ ∈ T := hcT _ (by show p ≤ a; omega) (by show a < q; omega)
    have hcl : copies ⟨a - 1, by omega⟩ ∈ T :=
      hcT _ (by show p ≤ a - 1; omega) (by show a - 1 < q; omega)
    have hcardL : TL.card < n := by
      refine hn ▸ Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨_, hca, ?_⟩)
      have hc : path (Fin.castSucc ⟨a, by omega⟩) = va := hpath_a _ rfl
      have hs : path (Fin.succ ⟨a, by omega⟩) = vr := by
        rw [hvr]
        rfl
      rcases h.ends ⟨a, by omega⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hc, hs]
        rintro (h3 | h3)
        · exact hvaL h3
        · exact hvrL h3
      · rw [h1, h2, hc, hs]
        rintro (h3 | h3)
        · exact hvrL h3
        · exact hvaL h3
    have hcardR : TR.card < n := by
      refine hn ▸ Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨_, hcl, ?_⟩)
      have hc : path (Fin.castSucc ⟨a - 1, by omega⟩) = vl := by
        rw [hvl]
        rfl
      have hs : path (Fin.succ ⟨a - 1, by omega⟩) = va := hpath_a _ (by simp; omega)
      have hvlR : vl ∉ R := hLR vl hvlL
      rcases h.ends ⟨a - 1, by omega⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hc, hs]
        rintro (h3 | h3)
        · exact hvlR h3
        · exact hvaR h3
      · rw [h1, h2, hc, hs]
        rintro (h3 | h3)
        · exact hvaR h3
        · exact hvlR h3
    have hpL : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ a → path i ∈ insert va L := by
      intro i hi1 hi2
      rcases eq_or_lt_of_le hi2 with hia | hia
      · rw [hpath_a i hia]
        exact mem_insert _ _
      · exact mem_insert_of_mem _ (hleft i hi1 hia)
    have hpR : ∀ i : Fin (m + 1), a ≤ (i : ℕ) → (i : ℕ) ≤ q → path i ∈ insert va R := by
      intro i hi1 hi2
      rcases eq_or_lt_of_le hi1 with hia | hia
      · rw [hpath_a i hia.symm]
        exact mem_insert _ _
      · exact mem_insert_of_mem _ (hright i hia hi2)
    have hcL : ∀ i : Fin m, p ≤ (i : ℕ) → (i : ℕ) < a → copies i ∈ TL := fun i hi1 hi2 =>
      Finset.mem_filter.mpr ⟨hcT i hi1 (by omega), copies_end_left h.ends i (hleft _ hi1 hi2)⟩
    have hcR : ∀ i : Fin m, a ≤ (i : ℕ) → (i : ℕ) < q → copies i ∈ TR := fun i hi1 hi2 =>
      Finset.mem_filter.mpr ⟨hcT i (by omega) hi2,
        copies_end_right h.ends i (hright i.succ (by simp; omega) (by simp; omega))⟩
    have hTSL : ∀ e ∈ TL, J.left e ∈ insert va L ∧ J.right e ∈ insert va L := by
      intro e he
      obtain ⟨heT, hmem⟩ := Finset.mem_filter.mp he
      exact reachSet_closed hvl_ne heT hmem
    have hTSR : ∀ e ∈ TR, J.left e ∈ insert va R ∧ J.right e ∈ insert va R := by
      intro e he
      obtain ⟨heT, hmem⟩ := Finset.mem_filter.mp he
      exact reachSet_closed hvr_ne heT hmem
    obtain ⟨Lr⟩ := ih _ hcardL (insert va L) TL rfl hpa (by omega) hpL hcL hTSL
    obtain ⟨Rr⟩ := ih _ hcardR (insert va R) TR rfl haq hqm hpR hcR hTSR
    have hSLR : ∀ v ∈ insert va L, v ∈ insert va R → v = path ⟨a, by omega⟩ := by
      intro v hv1 hv2
      rw [← hva]
      rcases hv1 with hv1 | hv1
      · exact hv1
      · rcases hv2 with hv2 | hv2
        · exact hv2
        · exact absurd hv2 (hLR v hv1)
    have hTLR : ∀ e ∈ (TL : Set E), e ∉ (TR : Set E) := by
      intro e he he'
      obtain ⟨heT, hmem⟩ := Finset.mem_filter.mp he
      obtain ⟨-, hmem'⟩ := Finset.mem_filter.mp he'
      obtain ⟨h1, h2⟩ := reachSet_closed hvl_ne heT hmem
      rcases hmem' with h3 | h3
      · rcases h1 with h1 | h1
        · exact hvaR (h1 ▸ h3)
        · exact hLR _ h1 h3
      · rcases h2 with h2 | h2
        · exact hvaR (h2 ▸ h3)
        · exact hLR _ h2 h3
    obtain ⟨C⟩ := SquareRealization.combine hpa haq hqm Lr Rr (fun e he => hTSL e he)
      (fun e he => hTSR e he) hSLR hpL hpR hTLR hcL hcR
    obtain ⟨Pd⟩ := hpend ((S \ L) \ R) TY
    have hTSY : ∀ e ∈ (TY : Set E), J.left e ∈ (S \ L) \ R ∧ J.right e ∈ (S \ L) \ R := by
      intro e he
      obtain ⟨heT, hmL, hmR⟩ := Finset.mem_filter.mp he
      exact ⟨⟨⟨(hTS e heT).1, fun h1 => hmL (Or.inl h1)⟩, fun h1 => hmR (Or.inl h1)⟩,
        ⟨⟨(hTS e heT).2, fun h1 => hmL (Or.inr h1)⟩, fun h1 => hmR (Or.inr h1)⟩⟩
    have hres := SquareRealization.insert hpa.le haq hqm C Pd subset_rfl subset_rfl
      (by
        rintro e (he | he)
        · obtain ⟨h1, h2⟩ := hTSL e he
          exact ⟨Or.inl h1, Or.inl h2⟩
        · obtain ⟨h1, h2⟩ := hTSR e he
          exact ⟨Or.inr h1, Or.inr h2⟩)
      hTSY
      (by
        intro v hv1 hv2
        rw [← hva]
        obtain ⟨⟨-, hvL⟩, hvR⟩ := hv2
        rcases hv1 with (hv1 | hv1) | (hv1 | hv1)
        · exact hv1
        · exact absurd hv1 hvL
        · exact hv1
        · exact absurd hv1 hvR)
      (by rw [← hva]; exact Or.inl (mem_insert _ _))
      (by rw [← hva]; exact ⟨⟨hvaS, hvaL⟩, hvaR⟩)
      (fun i hi1 hi2 => by
        by_cases hia : (i : ℕ) ≤ a
        · exact Or.inl (hpL i hi1 hia)
        · exact Or.inr (hpR i (by omega) hi2))
      (fun i hi1 hi2 => by
        by_cases hia : (i : ℕ) < a
        · exact Or.inl (hcL i hi1 hia)
        · exact Or.inr (hcR i (by omega) hi2))
    have hSe : (insert va L ∪ insert va R) ∪ (S \ L) \ R = S := by
      ext x
      constructor
      · rintro (((rfl | hx) | (rfl | hx)) | ⟨⟨hx, -⟩, -⟩)
        · exact hvaS
        · exact reachSet_subset hvlS hTS hx
        · exact hvaS
        · exact reachSet_subset hvrS hTS hx
        · exact hx
      · intro hx
        by_cases hxL : x ∈ L
        · exact Or.inl (Or.inl (mem_insert_of_mem _ hxL))
        · by_cases hxR : x ∈ R
          · exact Or.inl (Or.inr (mem_insert_of_mem _ hxR))
          · exact Or.inr ⟨⟨hx, hxL⟩, hxR⟩
    have hTe : ((TL : Set E) ∪ (TR : Set E)) ∪ (TY : Set E) = (T : Set E) := by
      ext e
      constructor
      · rintro ((he | he) | he)
        · exact Finset.mem_coe.mpr (Finset.mem_filter.mp he).1
        · exact Finset.mem_coe.mpr (Finset.mem_filter.mp he).1
        · exact Finset.mem_coe.mpr (Finset.mem_filter.mp he).1
      · intro he
        have he' : e ∈ T := Finset.mem_coe.mp he
        by_cases h1 : J.left e ∈ L ∨ J.right e ∈ L
        · exact Or.inl (Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨he', h1⟩)))
        · by_cases h2 : J.left e ∈ R ∨ J.right e ∈ R
          · exact Or.inl (Or.inr (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨he', h2⟩)))
          · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨he', h1, h2⟩))
    rw [hSe, hTe] at hres
    exact hres

end StraightPath

end Main

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
