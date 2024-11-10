import Language.Equiv

import Mathlib.Data.Finset.NAry

set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


namespace Language


inductive IsRegLang {α : Type} : Language α → Prop
| char
  (a : α) :
  IsRegLang {[a]}

| epsilon :
  IsRegLang {[]}

| zero :
  IsRegLang ∅

| union
  (R1 R2 : Language α) :
  IsRegLang R1 →
  IsRegLang R2 →
  IsRegLang (R1 ∪ R2)

| concat
  (R1 R2 : Language α) :
  IsRegLang R1 →
  IsRegLang R2 →
  IsRegLang (concat R1 R2)

| kleene_closure
  (R : Language α) :
  IsRegLang R →
  IsRegLang (kleene_closure α R)


theorem derivative_of_reg_lang_wrt_char_is_reg_lang
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (a : α)
  (h1 : IsRegLang R) :
  IsRegLang (derivative R [a]) :=
  by
    induction h1
    case char b =>
      by_cases c1 : a = b
      case pos =>
        rw [c1]
        simp only [derivative_of_char_wrt_same_char]
        exact IsRegLang.epsilon
      case neg =>
        simp only [derivative_of_char_wrt_diff_char a b c1]
        exact IsRegLang.zero
    case epsilon =>
      simp only [derivative_of_eps_wrt_char]
      exact IsRegLang.zero
    case zero =>
      simp only [derivative_of_empty_wrt_char]
      exact IsRegLang.zero
    case union R1 R2 ih_1 ih_2 ih_3 ih_4 =>
      simp only [derivative_of_union_wrt_char]
      exact IsRegLang.union (derivative R1 [a]) (derivative R2 [a]) ih_3 ih_4
    case concat R1 R2 ih_1 ih_2 ih_3 ih_4 =>
      simp only [derivative_of_concat_wrt_char]
      apply IsRegLang.union
      · exact IsRegLang.concat (derivative R1 [a]) R2 ih_3 ih_2
      · apply IsRegLang.concat
        · simp only [Language.nullify]
          split_ifs
          case pos c1 =>
            exact IsRegLang.epsilon
          case neg c1 =>
            exact IsRegLang.zero
        · exact ih_4
    case kleene_closure R' ih_1 ih_2 =>
      simp only [derivative_of_kleene_closure_wrt_char]
      apply IsRegLang.concat
      · exact ih_2
      · exact IsRegLang.kleene_closure R' ih_1


theorem derivative_of_reg_lang_wrt_str_is_reg_lang
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (s : Str α)
  (h1: IsRegLang R) :
  IsRegLang (derivative R s) :=
  by
    induction s generalizing R
    case nil =>
      simp only [derivative]
      simp
      exact h1
    case cons hd tl ih =>
      rw [derivative_wrt_cons]
      apply ih
      apply derivative_of_reg_lang_wrt_char_is_reg_lang
      exact h1


theorem all_derivative_of_reg_lang_wrt_str_mem_finset
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (h1: IsRegLang L) :
  ∃ (T : Finset (Language α)), ∀ (s : Str α), derivative L s ∈ T :=
  by
    open Classical in
    induction h1
    case char c =>
      apply Exists.intro {{}, {[]}, {[c]}}
      intro s
      cases s
      case nil =>
        rw [derivative_wrt_eps]
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        simp only [Finset.mem_singleton]
      case cons hd tl =>
        cases tl
        case nil =>
          by_cases c1 : hd = c
          case pos =>
            rw [c1]
            simp only [derivative_of_char_wrt_same_char c]
            apply Finset.mem_insert_of_mem
            exact Finset.mem_insert_self {[]} {{[c]}}
          case neg =>
            simp only [derivative_of_char_wrt_diff_char hd c c1]
            exact Finset.mem_insert_self ∅ {{[]}, {[c]}}
        case cons tl_hd tl_tl =>
          simp only [derivative]
          simp
    case epsilon =>
      apply Exists.intro {∅, {[]}}
      intro s
      cases s
      case nil =>
        simp only [derivative_wrt_eps]
        apply Finset.mem_insert_of_mem
        simp only [Finset.mem_singleton]
      case cons hd tl =>
        rw [derivative_wrt_cons]
        simp only [derivative_of_eps_wrt_char]
        simp only [derivative_of_empty_wrt_str]
        exact Finset.mem_insert_self ∅ {{[]}}
    case zero =>
      apply Exists.intro {∅}
      intro s
      simp only [derivative_of_empty_wrt_str]
      simp only [Finset.mem_singleton]
    case union L1 L2 L1_ih1 L2_ih1 L1_ih2 L2_ih2 =>
      simp only [derivative_of_union_wrt_str]

      obtain ⟨T1, a1⟩ := L1_ih2
      obtain ⟨T2, a2⟩ := L2_ih2

      apply Exists.intro (T1.biUnion (fun a => T2.biUnion (fun b => {a ∪ b})))
      simp
      intro s
      apply Exists.intro (derivative L1 s)
      constructor
      · exact a1 s
      · apply Exists.intro (derivative L2 s)
        constructor
        · exact a2 s
        . rfl
    case concat L1 L2 L1_ih1 L2_ih1 L1_ih2 L2_ih2 =>
      simp only [derivative_of_concat_wrt_str]

      obtain ⟨T1, a1⟩ := L1_ih2
      obtain ⟨T2, a2⟩ := L2_ih2

      let A := T1.biUnion (fun (M1 : Language α) => ({L2} : Finset (Language α)).biUnion (fun (M2 : Language α) => {concat M1 M2}))

      let B := T1.biUnion (fun (M1 : Language α) => T2.biUnion (fun (M2 : Language α) => {concat M1.nullify M2}))

      have s1 : ∀ (s : Str α), {M : Language α | ∃ (u : Str α) (v : Str α), u ++ v = s ∧ ¬ v = [] ∧ M = concat (derivative L1 u).nullify (derivative L2 v)} ⊆ B :=
      by
        intro s
        simp only [B]
        simp only [Set.subset_def]
        simp
        intro M u v _ _ a3
        apply Exists.intro (derivative L1 u)
        constructor
        · exact a1 u
        · apply Exists.intro (derivative L2 v)
          constructor
          · exact a2 v
          · exact a3

      have : ∀ (s : Str α), Finite {M : Language α | ∃ (u : Str α) (v : Str α), u ++ v = s ∧ ¬ v = [] ∧ M = concat (derivative L1 u).nullify (derivative L2 v)} :=
      by
        intro s
        exact Finite.Set.subset B (s1 s)


      let C := B.powerset.image (fun (S : Finset (Language α)) => S.toSet.sUnion)

      let T := A.biUnion (fun (M1 : Language α) => C.biUnion (fun (M2 : Language α) => {M1 ∪ M2}))

      apply Exists.intro T
      intro s
      simp only [T]
      simp only [A]
      simp only [C]
      simp

      apply Exists.intro (concat (derivative L1 s) L2)
      constructor
      · apply Exists.intro (derivative L1 s)
        constructor
        · exact a1 s
        · rfl
      · apply Exists.intro ({M : Language α | ∃ (u : Str α) (v : Str α), u ++ v = s ∧ ¬ v = [] ∧ M = concat (derivative L1 u).nullify (derivative L2 v)}).toFinite.toFinset
        constructor
        · simp only [Set.Finite.toFinset_subset]
          exact s1 s
        · simp only [List.length_pos]
          simp
    case kleene_closure L1 _ L1_ih2 =>
      obtain ⟨T, a1⟩ := L1_ih2

      have s1 : ∀ (s : Str α), {M : Language α | ∃ (t : List α), t ∈ foo' L1 s ∧ derivative L1 t = M} ⊆ T.toSet :=
      by
        intro s
        simp only [Set.subset_def]
        simp
        intro t _
        exact a1 t

      have s2 : ∀ (s : Str α), Finite {M : Language α | ∃ (t : List α), t ∈ foo' L1 s ∧ derivative L1 t = M} :=
      by
        intro s
        simp
        exact Set.Finite.subset (Finset.finite_toSet T) (s1 s)

      have s3 : ∀ (s : Str α), (⋃ t ∈ foo' L1 s, derivative L1 t) = ⋃₀ {M : Language α | ∃ (t : List α), t ∈ foo' L1 s ∧ derivative L1 t = M} :=
      by
        intro s
        ext cs
        simp

      have s4 : ∃ (S : Finset (Language α)), ∀ (s : Str α), (⋃ t ∈ foo' L1 s, derivative L1 t) ∈ S :=
      by
        simp only [s3]
        apply Exists.intro (T.powerset.image (fun (S : Finset (Language α)) => S.toSet.sUnion))
        intro s
        simp
        apply Exists.intro {M : Language α | ∃ (t : List α), t ∈ foo' L1 s ∧ derivative L1 t = M}.toFinite.toFinset
        simp
        exact s1 s

      obtain ⟨S, a2⟩ := s4

      let A := {kleene_closure α L1} ∪ S.biUnion (fun (M : Language α) => {concat M (kleene_closure α L1)})

      apply Exists.intro A
      intro s
      by_cases c1 : s = []
      case pos =>
        simp only [A]
        simp only [c1]
        simp only [derivative_wrt_eps]
        simp
      case neg =>
        obtain s1 := derivative_of_kleene_closure_wrt_str L1 s c1
        rw [s1]
        clear s1

        have s2 : ⋃ t ∈ foo' L1 s, concat (derivative L1 t) (kleene_closure α L1) = concat (⋃ t ∈ foo' L1 s, derivative L1 t) (kleene_closure α L1) :=
        by
          simp only [concat]
          simp
          ext cs
          simp
          constructor
          · intro a3
            obtain ⟨i, hi, s, hs, t, ht, eq⟩ := a3
            rw [← eq]
            exact ⟨s, ⟨i, hi, hs⟩, t, ht, rfl⟩
          · intro a3
            obtain ⟨s, ⟨i, hi, hs⟩, t, ht, eq⟩ := a3
            rw [← eq]
            exact ⟨i, hi, s, hs, t, ht, rfl⟩
        rw [s2]
        clear s2

        simp only [A]
        simp
        right
        apply Exists.intro (⋃ t ∈ foo' L1 s, derivative L1 t)
        exact ⟨a2 s, rfl⟩
