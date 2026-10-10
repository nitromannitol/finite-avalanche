import FiniteAvalanches.Electrical.Trees.RootedForestExchange
import FiniteAvalanches.Electrical.Trees.PathUniqueCrossing
import FiniteAvalanches.Electrical.Trees.SeparatingForestCompletionIff

/-! The numerator complement bijection for a split terminal star that is a literal dual path. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V W E : Type} [Fintype E]

/-- A literal denominator equivalence supplies the whole subset complement law. -/
theorem forest_tree_complement_iff_of_equiv (K : CopiedGraph V E) (B : CopiedGraph W E)
    (s t : V) (phi : K.TwoRootForest s t ≃ B.SpanningTree)
    (hphi : ∀ F, (phi F).val = F.valᶜ) (A : Finset E) :
    ((∀ e ∈ A, ¬K.reaches (A.erase e) (K.left e) (K.right e)) ∧
      ∀ x, ∃ r ∈ ({s, t} : Set V), K.reaches A x r ∧
        ∀ r' ∈ ({s, t} : Set V), K.reaches A x r' → r' = r) ↔
    ((Set.univ : Set W).Nonempty ∧ (∀ x y, B.reaches Aᶜ x y) ∧
      ∀ e ∈ Aᶜ, ¬B.reaches (Aᶜ.erase e) (B.left e) (B.right e)) := by
  constructor
  · intro h
    have ht := (phi ⟨A, h⟩).property
    rwa [hphi] at ht
  · intro h
    let T : B.SpanningTree := ⟨Aᶜ, h⟩
    have hv : (phi.symm T).val = A := by
      have he := hphi (phi.symm T)
      rw [phi.apply_symm_apply] at he
      have he' := congrArg (fun S : Finset E => Sᶜ) he
      simpa only [T, compl_compl] using he'.symm
    have hf := (phi.symm T).property
    rwa [hv] at hf

/-- Whole rooted-forest/tree complementation plus the actual terminal-star path gives
whole tree/separating-forest complementation. Loops and parallel IDs remain in E. -/
theorem terminal_tree_complement_iff
    (K : CopiedGraph V E) (B : CopiedGraph W E) (s t : V) (hst : s ≠ t)
    (hcomp : ∀ A : Finset E,
      ((∀ e ∈ A, ¬K.reaches (A.erase e) (K.left e) (K.right e)) ∧
        ∀ x, ∃ r ∈ ({s, t} : Set V), K.reaches A x r ∧
          ∀ r' ∈ ({s, t} : Set V), K.reaches A x r' → r' = r) ↔
      ((Set.univ : Set W).Nonempty ∧ (∀ x y, B.reaches Aᶜ x y) ∧
        ∀ e ∈ Aᶜ, ¬B.reaches (Aᶜ.erase e) (B.left e) (B.right e)))
    (m : ℕ) (vertices : Fin (m + 1) → W) (copies : Fin m → E)
    (hinj : Function.Injective copies)
    (hends : ∀ k : Fin m,
      (B.left (copies k) = vertices k.castSucc ∧ B.right (copies k) = vertices k.succ) ∨
      (B.right (copies k) = vertices k.castSucc ∧ B.left (copies k) = vertices k.succ))
    (i : Fin (m + 1)) (hne : vertices i ≠ vertices (Fin.last m))
    (hstar : ∀ e, (K.left e = t ∨ K.right e = t) ↔
      ∃ k : Fin m, i.val ≤ k.val ∧ copies k = e)
    (hloop : ∀ e, ¬(K.left e = t ∧ K.right e = t))
    (hunique : ∀ F : B.TwoRootForest (vertices i) (vertices (Fin.last m)),
      ∃! k : Fin m, i.val ≤ k.val ∧ ¬B.reaches F.val (B.left (copies k)) (B.right (copies k)))
    (A : Finset E) :
    ((Set.univ : Set V).Nonempty ∧ (∀ x y, K.reaches A x y) ∧
      ∀ e ∈ A, ¬K.reaches (A.erase e) (K.left e) (K.right e)) ↔
    ((∀ e ∈ Aᶜ, ¬B.reaches (Aᶜ.erase e) (B.left e) (B.right e)) ∧
      ∀ x, ∃ r ∈ ({vertices i, vertices (Fin.last m)} : Set W), B.reaches Aᶜ x r ∧
        ∀ r' ∈ ({vertices i, vertices (Fin.last m)} : Set W), B.reaches Aᶜ x r' → r' = r) := by
  constructor
  · intro hT
    let T : K.SpanningTree := ⟨A, hT⟩
    obtain ⟨c, hc, hct, hcut⟩ := forest_path_incident_exists K A hT.2.2 t s
      (Ne.symm hst) (hT.2.1 t s)
    have hcuts : ¬K.reaches (A.erase c) s t := fun h => hcut (TwoCopy.reaches_symm K h)
    let KF : K.TwoRootForest (K.left c) (K.right c) :=
      ⟨A.erase c, tree_erase_twoRootForest K T c hc⟩
    have hKF := twoRootForest_reroot K _ _ s t KF hcuts
    have hU := (hcomp (A.erase c)).mp hKF
    rw [Finset.compl_erase] at hU
    let U : B.SpanningTree := ⟨insert c Aᶜ, hU⟩
    have hcnot : c ∉ Aᶜ := Finset.notMem_compl.mpr hc
    have hFc := tree_erase_twoRootForest B U c (Finset.mem_insert_self _ _)
    change (∀ e ∈ (insert c Aᶜ).erase c,
      ¬B.reaches (((insert c Aᶜ).erase c).erase e) (B.left e) (B.right e)) ∧
      (∀ x, ∃ r ∈ ({B.left c, B.right c} : Set W),
        B.reaches ((insert c Aᶜ).erase c) x r ∧
        ∀ r' ∈ ({B.left c, B.right c} : Set W),
          B.reaches ((insert c Aᶜ).erase c) x r' → r' = r) at hFc
    rw [Finset.erase_insert hcnot] at hFc
    let F : B.TwoRootForest (B.left c) (B.right c) := ⟨Aᶜ, hFc⟩
    have hcsep : ¬B.reaches Aᶜ (B.left c) (B.right c) := by
      have h := U.property.2.2 c (Finset.mem_insert_self _ _)
      change ¬B.reaches ((insert c Aᶜ).erase c) (B.left c) (B.right c) at h
      rwa [Finset.erase_insert hcnot] at h
    obtain ⟨k, hik, hk⟩ := (hstar c).mp hct
    have cut_unique (l : Fin m) (hil : i.val ≤ l.val)
        (hl : ¬B.reaches Aᶜ (B.left (copies l)) (B.right (copies l))) : l = k := by
      have hB := twoRootForest_insert_tree B _ _ F (copies l) hl
      have hK := (hcomp (A.erase (copies l))).mpr (by
        rw [Finset.compl_erase]
        exact hB)
      let FL : K.TwoRootForest s t := ⟨A.erase (copies l), hK⟩
      have hlcut := twoRootForest_roots_separated K s t hst FL
      have hlt : K.left (copies l) = t ∨ K.right (copies l) = t :=
        (hstar (copies l)).mpr ⟨l, hil, rfl⟩
      have heq : c = copies l := tree_path_incident_unique K T t s c (copies l)
        hc hct hlt hcut (fun h => hlcut (TwoCopy.reaches_symm K h))
      exact hinj (heq.symm.trans hk.symm)
    have hs := path_unique_suffix_crossing_separates B Aᶜ m vertices copies hends i k hik
      (by rw [hk]; exact hcsep) cut_unique
    exact twoRootForest_reroot B _ _ _ _ F hs
  · intro hF
    let F : B.TwoRootForest (vertices i) (vertices (Fin.last m)) := ⟨Aᶜ, hF⟩
    obtain ⟨k, ⟨hik, hkcut⟩, hku⟩ := hunique F
    let c := copies k
    have hcnot : c ∉ Aᶜ := fun h => hkcut (.single ⟨c, h, Or.inl ⟨rfl, rfl⟩⟩)
    have hcA : c ∈ A := Finset.notMem_compl.mp hcnot
    have hct : K.left c = t ∨ K.right c = t := (hstar c).mpr ⟨k, hik, rfl⟩
    have hB := twoRootForest_insert_tree B _ _ F c hkcut
    have hKF := (hcomp (A.erase c)).mpr (by rw [Finset.compl_erase]; exact hB)
    let KF : K.TwoRootForest s t := ⟨A.erase c, hKF⟩
    have hcsep : ¬K.reaches (A.erase c) (K.left c) (K.right c) := by
      intro hcc
      have exists_other : ∃ e ∈ A.erase c, (K.left e = t ∨ K.right e = t) ∧
          ¬K.reaches ((A.erase c).erase e) (K.left c) (K.right c) := by
        rcases hct with hct | hct
        · have hnt : t ≠ K.right c := fun h => hloop c ⟨hct, h.symm⟩
          obtain ⟨e, he, het, hcut⟩ := forest_path_incident_exists K (A.erase c)
            hKF.1 t (K.right c) hnt (hct ▸ hcc)
          exact ⟨e, he, het, hct ▸ hcut⟩
        · have hnt : t ≠ K.left c := fun h => hloop c ⟨h.symm, hct⟩
          obtain ⟨e, he, het, hcut⟩ := forest_path_incident_exists K (A.erase c)
            hKF.1 t (K.left c) hnt (hct ▸ TwoCopy.reaches_symm K hcc)
          exact ⟨e, he, het, fun h => hcut (hct ▸ TwoCopy.reaches_symm K h)⟩
      obtain ⟨e, he, het, hcut⟩ := exists_other
      obtain ⟨l, hil, hl⟩ := (hstar e).mp het
      have hec : e ≠ c := (Finset.mem_erase.mp he).1
      have hx := twoRootForest_exchange K s t KF e c he hcc hcut
      have hval : insert c ((A.erase c).erase e) = A.erase e := by
        rw [Finset.erase_right_comm]
        exact Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hec, hcA⟩)
      rw [hval] at hx
      have hBE := (hcomp (A.erase e)).mp hx
      rw [Finset.compl_erase] at hBE
      have hecut := (twoRootForest_insert_tree_iff B _ _ hne F e).mp hBE
      have hlcut : ¬B.reaches F.val (B.left (copies l)) (B.right (copies l)) := by
        rw [hl]
        exact hecut
      have hlk := hku l ⟨hil, hlcut⟩
      exact hec (hl.symm.trans (congrArg copies hlk))
    have hKA := twoRootForest_insert_tree K s t KF c hcsep
    rwa [Finset.insert_erase hcA] at hKA

/-- Complement itself gives both maps; involution proves both inverse laws. -/
def treeTwoRootForestComplementEquiv (K : CopiedGraph V E) (B : CopiedGraph W E)
    (u v : W)
    (hcomp : ∀ A : Finset E,
      ((Set.univ : Set V).Nonempty ∧ (∀ x y, K.reaches A x y) ∧
        ∀ e ∈ A, ¬K.reaches (A.erase e) (K.left e) (K.right e)) ↔
      ((∀ e ∈ Aᶜ, ¬B.reaches (Aᶜ.erase e) (B.left e) (B.right e)) ∧
        ∀ x, ∃ r ∈ ({u, v} : Set W), B.reaches Aᶜ x r ∧
          ∀ r' ∈ ({u, v} : Set W), B.reaches Aᶜ x r' → r' = r)) :
    K.SpanningTree ≃ B.TwoRootForest u v where
  toFun T := ⟨T.valᶜ, (hcomp T.val).mp T.property⟩
  invFun F := ⟨F.valᶜ, (hcomp F.valᶜ).mpr (by
    rw [compl_compl]
    exact F.property)⟩
  left_inv T := Subtype.ext (compl_compl T.val)
  right_inv F := Subtype.ext (compl_compl F.val)

theorem treeTwoRootForestComplementEquiv_copies (K : CopiedGraph V E)
    (B : CopiedGraph W E) (u v : W)
    (hcomp : ∀ A : Finset E,
      ((Set.univ : Set V).Nonempty ∧ (∀ x y, K.reaches A x y) ∧
        ∀ e ∈ A, ¬K.reaches (A.erase e) (K.left e) (K.right e)) ↔
      ((∀ e ∈ Aᶜ, ¬B.reaches (Aᶜ.erase e) (B.left e) (B.right e)) ∧
        ∀ x, ∃ r ∈ ({u, v} : Set W), B.reaches Aᶜ x r ∧
          ∀ r' ∈ ({u, v} : Set W), B.reaches Aᶜ x r' → r' = r))
    (T : K.SpanningTree) :
    (treeTwoRootForestComplementEquiv K B u v hcomp T).val = T.valᶜ := rfl

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
