/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/PolyArcRealize.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.ArcCollars
import FiniteAvalanches.Support.Schoenflies.GeneralCrosscut
import FiniteAvalanches.Support.Schoenflies.Realization

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 
























































































open Metric Set unitInterval

namespace Schoenflies

open Plane

 





 

theorem exists_injective_extend {N : ℕ} (v : ℕ → Plane)
    (hv : ∀ i < N, ∀ j < N, v i = v j → i = j) :
    ∃ w : ℕ → Plane, Function.Injective w ∧ ∀ k < N, w k = v k := by
  classical
  
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k < N, v k 0 ≤ M := by
    obtain ⟨M, hM⟩ := ((Set.finite_lt_nat N).image fun k => v k 0).bddAbove
    exact ⟨M, fun k hk => hM ⟨k, hk, rfl⟩⟩
  refine ⟨fun k => if k < N then v k else Plane.mk (M + 1 + k) 0, ?_, fun k hk => by simp [hk]⟩
  intro k l hkl
  dsimp only at hkl
  by_cases hk : k < N <;> by_cases hl : l < N
  · rw [if_pos hk, if_pos hl] at hkl
    exact hv k hk l hl hkl
  · 
    exfalso
    rw [if_pos hk, if_neg hl] at hkl
    have h1 : v k 0 = M + 1 + (l : ℝ) := by rw [hkl]; exact Plane.mk_zero _ _
    have h2 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have h3 := hM k hk
    linarith
  · exfalso
    rw [if_neg hk, if_pos hl] at hkl
    have h1 : v l 0 = M + 1 + (k : ℝ) := by rw [← hkl]; exact Plane.mk_zero _ _
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h3 := hM l hl
    linarith
  · rw [if_neg hk, if_neg hl] at hkl
    have h1 : M + 1 + (k : ℝ) = M + 1 + (l : ℝ) := by
      rw [← Plane.mk_zero (M + 1 + (k : ℝ)) 0, hkl]; exact Plane.mk_zero _ _
    exact_mod_cast (by linarith : (k : ℝ) = (l : ℝ))

 






section SkipIdx

variable {i k : ℕ}

 
def skipIdx (i k : ℕ) : ℕ := if k ≤ i then k else k + 1

theorem skipIdx_of_le (h : k ≤ i) : skipIdx i k = k := if_pos h

theorem skipIdx_of_lt (h : i < k) : skipIdx i k = k + 1 := if_neg (by omega)

theorem skipIdx_injective (i : ℕ) : Function.Injective (skipIdx i) := by
  intro k l h
  simp only [skipIdx] at h
  split_ifs at h <;> omega

theorem skipIdx_succ (h : k ≠ i) : skipIdx i (k + 1) = skipIdx i k + 1 := by
  simp only [skipIdx]
  split_ifs <;> omega

theorem skipIdx_ne_left (h : k ≠ i) : skipIdx i k ≠ i := by
  simp only [skipIdx]; split_ifs <;> omega

theorem skipIdx_ne_right (i k : ℕ) : skipIdx i k ≠ i + 1 := by
  simp only [skipIdx]; split_ifs <;> omega

end SkipIdx

 





 

structure PreArc (n : ℕ) where
   
  vertex : ℕ → Plane
   
  vertex_inj : Function.Injective vertex
   
  edges_meet : ∀ i ≤ n, ∀ j ≤ n, i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}

namespace PreArc

variable {n i j k : ℕ}

 
def edge (A : PreArc n) (i : ℕ) : Set Plane := segment ℝ (A.vertex i) (A.vertex (i + 1))

 
def carrier (A : PreArc n) : Set Plane := ⋃ i, ⋃ (_ : i ≤ n), A.edge i

variable {A : PreArc n}

theorem mem_carrier_iff {x : Plane} : x ∈ A.carrier ↔ ∃ i ≤ n, x ∈ A.edge i := mem_iUnion_le_nat

theorem edge_subset_carrier (hi : i ≤ n) : A.edge i ⊆ A.carrier :=
  fun _ hx => mem_carrier_iff.2 ⟨i, hi, hx⟩

theorem vertex_ne : A.vertex i ≠ A.vertex (i + 1) := fun h => by
  have := A.vertex_inj h; omega

 




 


theorem edge_union_of_det_eq_zero (A : PreArc n) (hi : i < n)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    segment ℝ (A.vertex i) (A.vertex (i + 1 + 1)) = A.edge i ∪ A.edge (i + 1) :=
  segment_split (openSegment_subset_segment ℝ _ _
    (PrePolygon.mem_openSegment_of_det_eq_zero' vertex_ne
      (fun h => by have := A.vertex_inj h; omega)
      (A.edges_meet i (by omega) (i + 1) (by omega) (by omega)) hdet))

 

theorem vertex_notMem_edge (A : PreArc n) (hi : i < n) (hk : k ≤ n) (hk1 : k ≠ i)
    (hk2 : k ≠ i + 1) : A.vertex (i + 1) ∉ A.edge k := by
  intro hmem
  have h := A.edges_meet k hk i (by omega) hk1 ⟨hmem, right_mem_segment ℝ _ _⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h <;> exact absurd (A.vertex_inj h) (by omega)

 


theorem skip_edges_meet (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    ∀ j ≤ n, ∀ k ≤ n, j ≠ k →
      segment ℝ (A.vertex (skipIdx i j)) (A.vertex (skipIdx i (j + 1))) ∩
          segment ℝ (A.vertex (skipIdx i k)) (A.vertex (skipIdx i (k + 1))) ⊆
        {A.vertex (skipIdx i j), A.vertex (skipIdx i (j + 1))} := by
  
  have hplain : ∀ l, l ≠ i →
      segment ℝ (A.vertex (skipIdx i l)) (A.vertex (skipIdx i (l + 1))) = A.edge (skipIdx i l) :=
    fun l hl => by rw [skipIdx_succ hl]; rfl
  have hmerge : segment ℝ (A.vertex (skipIdx i i)) (A.vertex (skipIdx i (i + 1)))
      = A.edge i ∪ A.edge (i + 1) := by
    rw [skipIdx_of_le (le_refl i), skipIdx_of_lt (Nat.lt_succ_self i)]
    exact A.edge_union_of_det_eq_zero hi hdet
  have hle : ∀ l ≤ n, skipIdx i l ≤ n + 1 := by
    intro l hl; simp only [skipIdx]; split_ifs <;> omega
  intro j hj k hk hjk z hz
  by_cases hji : i = j
  · 
    subst hji
    have hk1 : skipIdx i k ≠ i := skipIdx_ne_left (Ne.symm hjk)
    have hk2 : skipIdx i k ≠ i + 1 := skipIdx_ne_right i k
    rw [skipIdx_of_le (le_refl i), skipIdx_of_lt (Nat.lt_succ_self i)]
    have hzk : z ∈ A.edge (skipIdx i k) := by
      rw [← hplain k (Ne.symm hjk)]; exact hz.2
    have hzj : z ∈ A.edge i ∪ A.edge (i + 1) := hmerge ▸ hz.1
    rcases hzj with hzj | hzj
    · have h := A.edges_meet i (by omega) (skipIdx i k) (hle k hk) (Ne.symm hk1) ⟨hzj, hzk⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact absurd (h ▸ hzk) (A.vertex_notMem_edge hi (hle k hk) hk1 hk2)
    · have h := A.edges_meet (i + 1) (by omega) (skipIdx i k) (hle k hk)
        (fun he => hk2 he.symm) ⟨hzj, hzk⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
      rcases h with h | h
      · exact absurd (h ▸ hzk) (A.vertex_notMem_edge hi (hle k hk) hk1 hk2)
      · exact Or.inr h
  · 
    have hji' : j ≠ i := fun he => hji he.symm
    rw [skipIdx_succ hji']
    have hzj : z ∈ A.edge (skipIdx i j) := (hplain j hji') ▸ hz.1
    by_cases hki : i = k
    · subst hki
      have hj1 : skipIdx i j ≠ i := skipIdx_ne_left hji'
      have hj2 : skipIdx i j ≠ i + 1 := skipIdx_ne_right i j
      rcases (hmerge ▸ hz.2 : z ∈ A.edge i ∪ A.edge (i + 1)) with hzk | hzk
      · exact A.edges_meet (skipIdx i j) (hle j hj) i (by omega) hj1 ⟨hzj, hzk⟩
      · exact A.edges_meet (skipIdx i j) (hle j hj) (i + 1) (by omega) hj2 ⟨hzj, hzk⟩
    · have hki' : k ≠ i := fun he => hki he.symm
      have hzk : z ∈ A.edge (skipIdx i k) := (hplain k hki') ▸ hz.2
      exact A.edges_meet (skipIdx i j) (hle j hj) (skipIdx i k) (hle k hk)
        (fun he => hjk (skipIdx_injective i he)) ⟨hzj, hzk⟩

 
def deleteVertex (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    PreArc n where
  vertex k := A.vertex (skipIdx i k)
  vertex_inj := A.vertex_inj.comp (skipIdx_injective i)
  edges_meet := A.skip_edges_meet hi hdet

@[simp] theorem deleteVertex_vertex (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0)
    (k : ℕ) : (A.deleteVertex hi hdet).vertex k = A.vertex (skipIdx i k) := rfl

theorem deleteVertex_vertex_zero (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    (A.deleteVertex hi hdet).vertex 0 = A.vertex 0 := by
  rw [deleteVertex_vertex, skipIdx_of_le (Nat.zero_le i)]

theorem deleteVertex_vertex_last (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    (A.deleteVertex hi hdet).vertex (n + 1) = A.vertex (n + 1 + 1) := by
  rw [deleteVertex_vertex, skipIdx_of_lt (by omega)]

 
theorem carrier_deleteVertex (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    (A.deleteVertex hi hdet).carrier = A.carrier := by
  have hplain : ∀ l, l ≠ i → (A.deleteVertex hi hdet).edge l = A.edge (skipIdx i l) :=
    fun l hl => by rw [edge, deleteVertex_vertex, deleteVertex_vertex, skipIdx_succ hl]; rfl
  have hmerge : (A.deleteVertex hi hdet).edge i = A.edge i ∪ A.edge (i + 1) := by
    rw [edge, deleteVertex_vertex, deleteVertex_vertex, skipIdx_of_le (le_refl i),
      skipIdx_of_lt (Nat.lt_succ_self i)]
    exact A.edge_union_of_det_eq_zero hi hdet
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨l, hl, hzl⟩ := mem_carrier_iff.1 hz
    by_cases hli : l = i
    · subst hli
      rcases (hmerge ▸ hzl : z ∈ A.edge l ∪ A.edge (l + 1)) with h | h
      exacts [edge_subset_carrier (by omega) h, edge_subset_carrier (by omega) h]
    · refine edge_subset_carrier (show skipIdx i l ≤ n + 1 by simp only [skipIdx]; split_ifs <;>
        omega) ((hplain l hli) ▸ hzl)
  · obtain ⟨l, hl, hzl⟩ := mem_carrier_iff.1 hz
    rcases Nat.lt_trichotomy l i with hlt | heq | hgt
    · refine mem_carrier_iff.2 ⟨l, by omega, ?_⟩
      rw [hplain l (by omega), skipIdx_of_le (by omega)]
      exact hzl
    · exact mem_carrier_iff.2 ⟨i, by omega, hmerge ▸ Or.inl (heq ▸ hzl)⟩
    · rcases Nat.lt_or_ge (i + 1) l with hlt' | hle'
      · refine mem_carrier_iff.2 ⟨l - 1, by omega, ?_⟩
        rw [hplain (l - 1) (by omega), skipIdx_of_lt (by omega), show l - 1 + 1 = l by omega]
        exact hzl
      · exact mem_carrier_iff.2 ⟨i, by omega, hmerge ▸ Or.inr (show l = i + 1 by omega ▸ hzl)⟩

 



theorem exists_polyArc : ∀ (n : ℕ) (A : PreArc n), ∃ (m : ℕ) (B : PolyArc m),
    B.carrier = A.carrier ∧ B.vertex 0 = A.vertex 0 ∧ B.vertex (m + 1) = A.vertex (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro A
      exact ⟨0, ⟨A.vertex, A.vertex_inj, A.edges_meet, fun i hi => absurd hi (Nat.not_lt_zero i)⟩,
        rfl, rfl, rfl⟩
  | succ n ih =>
      intro A
      by_cases hc : ∀ i < n + 1,
          det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 2) - A.vertex (i + 1)) ≠ 0
      · exact ⟨n + 1, ⟨A.vertex, A.vertex_inj, A.edges_meet, hc⟩, rfl, rfl, rfl⟩
      · push Not at hc
        obtain ⟨i, hi, hdet⟩ := hc
        obtain ⟨m, B, hcar, h0, hlast⟩ := ih (A.deleteVertex hi hdet)
        exact ⟨m, B, by rw [hcar, carrier_deleteVertex],
          by rw [h0, deleteVertex_vertex_zero], by rw [hlast, deleteVertex_vertex_last]⟩

end PreArc

 












 

theorem exists_preArc_of_isArcBetween {P : Set Plane} {a b : Plane}
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) :
    ∃ (n : ℕ) (A : PreArc n), A.carrier = P ∧ A.vertex 0 = a ∧ A.vertex (n + 1) = b := by
  classical
  obtain ⟨f, hcont, hinj, hfP, hf0, hf1⟩ := hP
  have hIco : ∀ s ∈ Ico (0 : ℝ) 1, s ∈ I := fun s hs => ⟨hs.1, hs.2.le⟩
  have hmemP : ∀ s ∈ I, f s ∈ P := fun s hs => hfP ▸ ⟨s, hs, rfl⟩
  have haP : a ∈ P := by rw [← hf0]; exact hmemP 0 zero_mem_I
  have hbP : b ∈ P := by rw [← hf1]; exact hmemP 1 one_mem_I
  have hab : a ≠ b := by
    rw [← hf0, ← hf1]
    exact fun he => absurd (hinj zero_mem_I one_mem_I he) (by norm_num)
  
  obtain ⟨Q, hQ, hextra⟩ := exists_isClean hpoly haP hbP hab [a, b]
  obtain ⟨Ra, hRa, hRaend⟩ := hextra a (by simp) haP
  obtain ⟨Rb, hRb, hRbend⟩ := hextra b (by simp) hbP
  have h0V : f 0 ∈ endSet Q := by rw [hf0]; exact ⟨Ra, hRa, hRaend⟩
  have h1V : f 1 ∈ endSet Q := by rw [hf1]; exact ⟨Rb, hRb, hRbend⟩
  
  have hsurj : ∀ z ∈ P \ endSet Q, ∃ s ∈ Ico (0 : ℝ) 1, f s = z := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ I, f s = z := by rw [← hfP] at hz; exact hz.1
    refine ⟨s, ⟨hs.1, ?_⟩, rfl⟩
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact absurd h1V hz.2
    · exact hlt
  
  have hTfin : {t : ℝ | t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q}.Finite := by
    refine Set.Finite.of_finite_image (f := f) ((finite_endSet Q).subset ?_)
      (hinj.mono fun t ht => hIco t ht.1)
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  obtain ⟨n, hcard⟩ : ∃ n, hTfin.toFinset.card = n := ⟨_, rfl⟩
  set TF : Finset ℝ := hTfin.toFinset with hTFdef
  have hmemTF : ∀ t : ℝ, t ∈ TF ↔ (t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q) := by
    intro t; rw [hTFdef, Set.Finite.mem_toFinset]; exact Iff.rfl
  have hTle : ∀ s ∈ TF, s ∈ Ico (0 : ℝ) 1 := fun s hs => ((hmemTF s).1 hs).1
  have h0TF : (0 : ℝ) ∈ TF := (hmemTF 0).2 ⟨⟨le_refl 0, by norm_num⟩, h0V⟩
  set tp : Fin n → ℝ := par TF hcard with htp
  set nx : Fin n → ℝ := parNext TF hcard with hnx
  
  have htpV : ∀ i : Fin n, f (tp i) ∈ endSet Q := fun i =>
    ((hmemTF _).1 (par_mem hcard i)).2
  have hnxV : ∀ i : Fin n, f (nx i) ∈ endSet Q := by
    intro i
    rw [hnx, parNext]
    split_ifs with hi
    · exact ((hmemTF _).1 (Finset.orderEmbOfFin_mem _ _ _)).2
    · exact h1V
  have hlt : ∀ i : Fin n, tp i < nx i := fun i => par_lt_parNext hcard hTle i
  have hIcc : ∀ i : Fin n, Icc (tp i) (nx i) ⊆ I := fun i => gapClosure_subset_I hcard hTle i
  have hIoo : ∀ i : Fin n, Ioo (tp i) (nx i) ⊆ Ico (0 : ℝ) 1 := fun i =>
    gap_subset_Ico hcard hTle i
  set G : Fin n → Set Plane := fun i => f '' Ioo (tp i) (nx i) with hG
  set Z : Fin n → Set Plane := fun i => f '' Icc (tp i) (nx i) with hZ
  have hGne : ∀ i, (G i).Nonempty := fun i => ((Set.nonempty_Ioo.2 (hlt i)).image f)
  have hGconn : ∀ i, IsPreconnected (G i) := fun i =>
    isPreconnected_Ioo.image f (hcont.mono (fun s hs => hIcc i (Ioo_subset_Icc_self hs)))
  have hGdiff : ∀ i, G i ⊆ P \ endSet Q := by
    rintro i z ⟨s, hs, rfl⟩
    refine ⟨hmemP s (hIcc i (Ioo_subset_Icc_self hs)), fun hzV => ?_⟩
    exact notMem_of_mem_gap hcard hs ((hmemTF s).2 ⟨hIoo i hs, hzV⟩)
  have hZcompact : ∀ i, IsCompact (Z i) := fun i =>
    isCompact_image_of_subset_I hcont (hIcc i) isClosed_Icc
  have hZeq : ∀ i, Z i = G i ∪ {f (tp i), f (nx i)} := by
    intro i
    simp only [hZ, hG]
    rw [Icc_eq_Ioo_union_ends (hlt i).le, Set.image_union, Set.image_pair]
  have hZdiff : ∀ i, Z i ∩ (P \ endSet Q) = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (fun z hz => ⟨(hZeq i) ▸ Or.inl hz, hGdiff i hz⟩)
    rintro z ⟨hzZ, hzC, hzV⟩
    rcases (hZeq i) ▸ hzZ with hz | hz
    · exact hz
    · rcases hz with rfl | rfl
      exacts [absurd (htpV i) hzV, absurd (hnxV i) hzV]
  have hGdisj : ∀ i j : Fin n, i ≠ j → G i ∩ G j = ∅ := by
    intro i j hij
    refine Set.eq_empty_of_forall_notMem ?_
    rintro z ⟨⟨s, hs, rfl⟩, t, ht, hts⟩
    have := hinj (hIco _ (hIoo j ht)) (hIco _ (hIoo i hs)) hts
    exact Set.disjoint_left.1 (gap_disjoint hcard hij) hs (this ▸ ht)
  
  have hcov : (⋃ i, G i) = P \ endSet Q := by
    refine Set.Subset.antisymm (Set.iUnion_subset hGdiff) (fun z hz => ?_)
    obtain ⟨s, hs, rfl⟩ := hsurj z hz
    obtain ⟨i, hi⟩ := exists_mem_gap hcard hTle h0TF hs
      (fun hsT => hz.2 ((hmemTF s).1 hsT).2)
    exact Set.mem_iUnion.2 ⟨i, ⟨s, hi, rfl⟩⟩
  
  have hchoose : ∀ i, ∃ R ∈ Q, G i ⊆ R.interior := fun i =>
    hQ.preconnected_subset_interior (hGconn i) (hGne i) (hGdiff i)
  choose pc hpcQ hpcsub using hchoose
  
  have hpceq : ∀ i, (pc i).interior = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (hpcsub i)
    set W : Set Plane := ⋃ j ∈ ({i}ᶜ : Set (Fin n)), Z j with hW
    have hWclosed : IsClosed W :=
      Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ => (hZcompact j).isClosed
    have hAdiff : (pc i).interior ⊆ P \ endSet Q := by
      rw [hQ.diff_endSet_eq]
      exact fun z hz => Set.mem_iUnion₂.2 ⟨pc i, hpcQ i, hz⟩
    have hAZ : (pc i).interior ⊆ Z i ∪ W := by
      intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov.symm ▸ hAdiff hz)
      by_cases hji : j = i
      · exact Or.inl ((hZeq i) ▸ Or.inl (hji ▸ hj))
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, (hZeq j) ▸ Or.inl hj⟩)
    have hGW : ∀ z ∈ G i, z ∉ W := by
      intro z hz hzW
      obtain ⟨j, hji, hzj⟩ := Set.mem_iUnion₂.1 hzW
      have : z ∈ G j := (hZdiff j) ▸ ⟨hzj, hGdiff i hz⟩
      exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j (Ne.symm hji)) z ⟨hz, this⟩
    have hcover2 : (pc i).interior ⊆ Wᶜ ∪ (Z i)ᶜ := by
      intro z hz
      by_cases hzW : z ∈ W
      · exact Or.inr fun hzZ => hGW z ((hZdiff i) ▸ ⟨hzZ, hAdiff hz⟩) hzW
      · exact Or.inl hzW
    have hnone : ¬ ((pc i).interior ∩ (Wᶜ ∩ (Z i)ᶜ)).Nonempty := by
      rintro ⟨z, hz, hzW, hzZ⟩
      rcases hAZ hz with h | h
      exacts [hzZ h, hzW h]
    have hconv : IsPreconnected ((pc i).interior) := (convex_openSegment _ _).isPreconnected
    obtain ⟨z₀, hz₀⟩ := hGne i
    have hAu : ((pc i).interior ∩ Wᶜ).Nonempty := ⟨z₀, hpcsub i hz₀, hGW z₀ hz₀⟩
    have hnotv : ¬ ((pc i).interior ∩ (Z i)ᶜ).Nonempty := fun hv =>
      hnone (hconv _ _ hWclosed.isOpen_compl (hZcompact i).isClosed.isOpen_compl hcover2 hAu hv)
    intro z hz
    have hzZ : z ∈ Z i := by
      by_contra hzZ
      exact hnotv ⟨z, hz, hzZ⟩
    exact (hZdiff i) ▸ ⟨hzZ, hAdiff hz⟩
  
  have hpcinj : Function.Injective pc := by
    intro i j hij
    by_contra hne'
    obtain ⟨z, hz⟩ := hGne i
    have hzj : z ∈ G j := by rw [← hpceq j, ← hij, hpceq i]; exact hz
    exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j hne') z ⟨hz, hzj⟩
  have hpcsurj : ∀ R ∈ Q, ∃ i, pc i = R := by
    intro R hR
    have hx : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ R.interior :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hxd : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ P \ endSet Q := by
      rw [hQ.diff_endSet_eq]; exact Set.mem_iUnion₂.2 ⟨R, hR, hx⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov.symm ▸ hxd)
    refine ⟨i, ?_⟩
    by_contra hne'
    exact hQ.interiors (pc i) (hpcQ i) R hR hne' _ (hpceq i ▸ hi) hx
  
  have hends : ∀ i, ((pc i).1 = f (tp i) ∧ (pc i).2 = f (nx i)) ∨
      ((pc i).1 = f (nx i) ∧ (pc i).2 = f (tp i)) := by
    intro i
    have hnd : (pc i).1 ≠ (pc i).2 := hQ.nondeg _ (hpcQ i)
    have hclosure : (pc i).seg ⊆ Z i := by
      have hcl : closure ((pc i).interior) ⊆ Z i := by
        rw [hpceq i]
        exact closure_minimal (fun z hz => (hZeq i) ▸ Or.inl hz) (hZcompact i).isClosed
      rwa [Piece.interior, closure_openSegment] at hcl
    have hmem : ∀ z, z = (pc i).1 ∨ z = (pc i).2 → z = f (tp i) ∨ z = f (nx i) := by
      intro z hz
      have hzseg : z ∈ (pc i).seg := by
        rcases hz with rfl | rfl
        exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
      rcases (hZeq i) ▸ hclosure hzseg with hzG | hzE
      · exfalso
        rw [← hpceq i] at hzG
        rcases hz with rfl | rfl
        exacts [hnd (left_mem_openSegment_iff.1 hzG), hnd (right_mem_openSegment_iff.1 hzG)]
      · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzE
    exact pair_eq_of_mem_pair hnd (hmem _ (Or.inl rfl)) (hmem _ (Or.inr rfl))
  have hpcseg : ∀ i, (pc i).seg = segment ℝ (f (tp i)) (f (nx i)) := by
    intro i
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Piece.seg, h1, h2]
    · rw [Piece.seg, h1, h2, segment_symm]
  
  have hn0 : 0 < n := par_card_pos hcard h0TF
  have htp0 : tp ⟨0, hn0⟩ = 0 := par_zero hcard hTle h0TF
  
  set vf : ℕ → Plane := fun k => if h : k < n then f (par TF hcard ⟨k, h⟩) else b with hvf
  have hvflt : ∀ (k : ℕ) (hk : k < n), vf k = f (tp ⟨k, hk⟩) := by
    intro k hk; rw [hvf]; simp only [dif_pos hk, htp]
  have hvfn : vf n = b := by rw [hvf]; simp only [dif_neg (lt_irrefl n)]
  
  have hvfsucc : ∀ (k : ℕ) (hk : k < n), vf (k + 1) = f (nx ⟨k, hk⟩) := by
    intro k hk
    by_cases hk1 : k + 1 < n
    · rw [hvflt (k + 1) hk1, htp, hnx, parNext,
        dif_pos (show (⟨k, hk⟩ : Fin n).val + 1 < n from hk1)]
      rfl
    · have : k + 1 = n := by omega
      rw [this, hvfn, hnx, parNext,
        dif_neg (show ¬ ((⟨k, hk⟩ : Fin n).val + 1 < n) from hk1), hf1]
  
  have hvfinj : ∀ i < n + 1, ∀ j < n + 1, vf i = vf j → i = j := by
    have hkey : ∀ i < n, ∀ j < n, vf i = vf j → i = j := by
      intro i hi j hj he
      rw [hvflt i hi, hvflt j hj] at he
      have h1 := hinj (hIco _ (hTle _ (par_mem hcard ⟨i, hi⟩)))
        (hIco _ (hTle _ (par_mem hcard ⟨j, hj⟩))) he
      exact congrArg Fin.val ((TF.orderEmbOfFin hcard).injective h1)
    have hlast : ∀ i < n, vf i ≠ vf n := by
      intro i hi he
      rw [hvflt i hi, hvfn, ← hf1] at he
      have h1 := hinj (hIco _ (hTle _ (par_mem hcard ⟨i, hi⟩))) one_mem_I he
      exact absurd (h1 ▸ (hTle _ (par_mem hcard ⟨i, hi⟩)).2) (lt_irrefl 1)
    intro i hi j hj he
    rcases Nat.lt_or_ge i n with hi' | hi'
    · rcases Nat.lt_or_ge j n with hj' | hj'
      · exact hkey i hi' j hj' he
      · exact absurd (show j = n by omega ▸ he) (hlast i hi')
    · rcases Nat.lt_or_ge j n with hj' | hj'
      · exact absurd (show i = n by omega ▸ he.symm) (hlast j hj')
      · omega
  obtain ⟨w, hwinj, hwval⟩ := exists_injective_extend vf hvfinj
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  
  have hwedge : ∀ (i : ℕ) (hi : i < m + 1),
      segment ℝ (w i) (w (i + 1)) = (pc ⟨i, hi⟩).seg := by
    intro i hi
    rw [hwval i (by omega), hwval (i + 1) (by omega), hvflt i hi, hvfsucc i hi, hpcseg]
  
  have hmeet : ∀ i ≤ m, ∀ j ≤ m, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)} := by
    intro i hi j hj hij
    rw [hwedge i (by omega), hwedge j (by omega)]
    have hne' : pc ⟨i, by omega⟩ ≠ pc ⟨j, by omega⟩ := fun he =>
      hij (congrArg Fin.val (hpcinj he))
    refine le_trans (hQ.seg_inter_subset (hpcQ _) (hpcQ _) hne') ?_
    have hwi : w i = f (tp ⟨i, by omega⟩) := by rw [hwval i (by omega), hvflt i (by omega)]
    have hwi' : w (i + 1) = f (nx ⟨i, by omega⟩) := by
      rw [hwval (i + 1) (by omega), hvfsucc i (by omega)]
    rcases hends ⟨i, by omega⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, ← hwi, ← hwi']
    · rw [h1, h2, ← hwi, ← hwi', Set.pair_comm]
  
  have hcarrier : (⋃ i, ⋃ (_ : i ≤ m), segment ℝ (w i) (w (i + 1))) = P := by
    rw [← hQ.cover_eq]
    refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨i, hi, hzi⟩ := mem_iUnion_le_nat.1 hz
      rw [hwedge i (by omega)] at hzi
      exact mem_cover (hpcQ _) hzi
    · obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
      obtain ⟨i, rfl⟩ := hpcsurj R hR
      refine mem_iUnion_le_nat.2 ⟨i.val, by omega, ?_⟩
      rw [hwedge i.val i.isLt]
      exact hzR
  have hzero : w 0 = a := by rw [hwval 0 (by omega), hvflt 0 hn0, htp0, hf0]
  have hlastv : w (m + 1) = b := by rw [hwval (m + 1) (by omega), hvfn]
  exact ⟨m, ⟨w, hwinj, hmeet⟩, hcarrier, hzero, hlastv⟩

 




 




theorem isPolyArcCarrier_of_isPolygonal {P : Set Plane} {a b : Plane}
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) : IsPolyArcCarrier P a b := by
  obtain ⟨n, A, hcar, h0, hlast⟩ := exists_preArc_of_isArcBetween hP hpoly
  obtain ⟨m, B, hcar', h0', hlast'⟩ := PreArc.exists_polyArc n A
  exact ⟨m, B, by rw [hcar', hcar], by rw [h0', h0], by rw [hlast', hlast]⟩

 

theorem hasArcCollars_of_isPolygonal {D P : Set Plane} {a b : Plane} (hD : IsOpen D)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) : HasArcCollars D P :=
  hasArcCollars hD ha hb hPD (isPolyArcCarrier_of_isPolygonal hP hpoly)

 

theorem crosscut_at_most_two_of_isPolygonal {D P : Set Plane} {a b : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D) :
    ∃ zL ∈ D \ P, ∃ zR ∈ D \ P, ∀ x ∈ D \ P,
      x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR :=
  crosscut_at_most_two hDopen hDconn hP hPpoly ha hb hPD
    (hasArcCollars_of_isPolygonal hDopen ha hb hPD hP hPpoly)

 

theorem crosscut_components_exhaust_of_isPolygonal {D P : Set Plane} {a b v₁ v₂ : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (h₁ : v₁ ∈ D \ P) (h₂ : v₂ ∈ D \ P)
    (hne : connectedComponentIn (D \ P) v₁ ≠ connectedComponentIn (D \ P) v₂) :
    ∀ x ∈ D \ P, x ∈ connectedComponentIn (D \ P) v₁ ∨ x ∈ connectedComponentIn (D \ P) v₂ :=
  crosscut_components_exhaust hDopen hDconn hP hPpoly ha hb hPD
    (hasArcCollars_of_isPolygonal hDopen ha hb hPD hP hPpoly) h₁ h₂ hne

 






variable {C P A₁ A₂ : Set Plane} {p q : Plane}

 
theorem IsCrosscut.hasArcCollars (h : IsCrosscut C P p q) : HasArcCollars (inside C) P :=
  Schoenflies.hasArcCollars (isOpen_inside h.curve.isClosed) h.left_notMem_inside
    h.right_notMem_inside h.sdiff_subset (isPolyArcCarrier_of_isPolygonal h.arc h.polygonal)

 

theorem general_crosscut' (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧ closure (inside (A₂ ∪ P)) ∩ C = A₂ :=
  general_crosscut hjordan h hcut h.hasArcCollars

 

theorem general_crosscut_three_regions'
    (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    (C ∪ P)ᶜ = outside C ∪ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      (∀ z ∈ outside C, connectedComponentIn (C ∪ P)ᶜ z = outside C) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ (C ∪ P)ᶜ, connectedComponentIn (C ∪ P)ᶜ z = outside C ∨
        connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P) ∨
        connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P)) ∧
      Disjoint (outside C) (inside (A₁ ∪ P)) ∧ Disjoint (outside C) (inside (A₂ ∪ P)) ∧
        Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      outside C ≠ inside (A₁ ∪ P) ∧ outside C ≠ inside (A₂ ∪ P) ∧
        inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      frontier (outside C) = C ∧ frontier (inside (A₁ ∪ P)) = A₁ ∪ P ∧
        frontier (inside (A₂ ∪ P)) = A₂ ∪ P :=
  general_crosscut_three_regions hjordan h hcut h.hasArcCollars

end Schoenflies
