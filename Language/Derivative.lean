import Language.Nullable


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


namespace Language


/-
Definition 15 (String derivative). The derivative of a language L ⊆ Σ∗ with respect to a string s ∈ Σ∗ is defined to be ∂sL = {t : s · t ∈ L}.
-/

def derivative
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Language α :=
  { t : Str α | s ++ t ∈ L }


lemma derivative_def
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α)
  (s : Str α) :
  s ∈ (derivative L [a]) ↔ a :: s ∈ L :=
  by
    simp only [derivative]
    simp


def derivative_list
  {α : Type}
  [DecidableEq α]
  (L : List (List α))
  (s : List α) :
  List (List α) :=
  (L.filter (fun (cs : List α) => List.IsPrefix s cs)).map
    (fun (cs : List α) => cs.drop s.length)


lemma derivative_eq_derivative_list
  {α : Type}
  [DecidableEq α]
  (L : List (List α))
  (s : List α) :
  derivative L.toFinset.toSet s = (derivative_list L s).toFinset.toSet :=
  by
    ext t
    simp only [derivative]
    simp only [derivative_list]
    simp
    simp only [List.IsPrefix]
    constructor
    · intro a1
      apply Exists.intro (s ++ t)
      simp
      exact a1
    · intro a1
      obtain ⟨xs, ⟨a2, cs, a3⟩, a4⟩ := a1
      rw [← a3] at a4
      simp at a4
      rw [← a4]
      rw [a3]
      exact a2


theorem derivative_wrt_eps
  {α : Type}
  (L : Language α) :
  derivative L [] = L :=
  by
    simp only [derivative]
    simp


theorem derivative_wrt_append
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  derivative L (s ++ t) = derivative (derivative L s) t :=
  by
    simp only [derivative]
    simp


theorem derivative_wrt_cons
  {α : Type}
  (L : Language α)
  (hd : α)
  (tl : Str α) :
  derivative L (hd :: tl) = derivative (derivative L [hd]) tl :=
  by
    simp only [derivative]
    simp


example
  {α : Type}
  (L : Language α)
  (s : Str α)
  (a : α) :
  derivative L (s ++ [a]) = derivative (derivative L s) [a] :=
  by
    simp only [derivative]
    simp


def derivative_wrt_str
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Language α :=
  List.foldl (fun (M : Language α) (c : α) => derivative M [c]) L s


example
  {α : Type}
  (L : Language α)
  (s : Str α) :
  derivative L s = derivative_wrt_str L s :=
  by
    simp only [derivative_wrt_str]
    induction s generalizing L
    case nil =>
      simp only [derivative]
      simp
    case cons hd tl ih =>
      have s1 : hd :: tl = [hd] ++ tl := rfl
      rw [s1]
      simp only [derivative_wrt_append]
      simp
      exact ih (derivative L [hd])


-- [a] ∈ Σ^1

-- 1.50
theorem derivative_of_empty_wrt_char
  {α : Type}
  (a : α) :
  derivative ∅ [a] = ∅ :=
  by
    simp only [derivative]
    simp


theorem derivative_of_empty_wrt_str
  {α : Type}
  (s : Str α) :
  derivative ∅ s = ∅ :=
  by
    simp only [derivative]
    simp


-- 1.51
theorem derivative_of_eps_wrt_char
  {α : Type}
  (a : α) :
  derivative {[]} [a] = ∅ :=
  by
    simp only [derivative]
    simp


-- 1.52
theorem derivative_of_char_wrt_same_char
  {α : Type}
  (a : α) :
  derivative {[a]} [a] = {[]} :=
  by
    simp only [derivative]
    simp


theorem derivative_of_str_wrt_same_str
  {α : Type}
  (s : Str α) :
  derivative {s} s = {[]} :=
  by
    simp only [derivative]
    simp


-- 1.53
theorem derivative_of_char_wrt_diff_char
  {α : Type}
  (a b : α)
  (h1 : ¬ a = b) :
  derivative {[b]} [a] = ∅ :=
  by
    simp only [derivative]
    simp
    simp only [h1]
    simp


-- 1.54
theorem derivative_of_union_wrt_char
  {α : Type}
  (L1 L2 : Language α)
  (a : α) :
  derivative (L1 ∪ L2) [a] =
    (derivative L1 [a]) ∪ (derivative L2 [a]) :=
  by
    simp only [derivative]
    rfl


theorem derivative_of_union_wrt_str
  {α : Type}
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (L1 ∪ L2) s =
    (derivative L1 s) ∪ (derivative L2 s) :=
  by
    simp only [derivative]
    rfl


-- 1.55
theorem derivative_of_intersection_wrt_char
  {α : Type}
  (L1 L2 : Language α)
  (a : α) :
  derivative (L1 ∩ L2) [a] =
    (derivative L1 [a]) ∩ (derivative L2 [a]) :=
  by
    simp only [derivative]
    rfl


theorem derivative_of_intersection_wrt_str
  {α : Type}
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (L1 ∩ L2) s =
    (derivative L1 s) ∩ (derivative L2 s) :=
  by
    simp only [derivative]
    rfl


lemma concat_nullify_and_derivative_wrt_char
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : α) :
  {s | a :: s ∈ (concat L1.nullify L2)} = concat L1.nullify (derivative L2 [a]) :=
  by
    simp only [derivative]
    simp only [concat]
    simp
    ext cs
    simp
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp at eq
        rw [eq] at ht
        exact ⟨[], hs, cs, ⟨ht, by simp⟩⟩
      case cons s_hd s_tl =>
        simp only [Language.nullify] at hs
        simp at hs
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp at eq
        rw [eq] at ht
        exact ⟨[], hs, (a :: cs), ht, by simp⟩
      case cons s_hd s_tl s_ih =>
        simp only [Language.nullify] at hs
        simp at hs


lemma concat_nullify_and_derivative_wrt_str
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : Str α) :
  {s | a ++ s ∈ (concat L1.nullify L2)} = concat L1.nullify (derivative L2 a) :=
  by
    simp only [derivative]
    simp only [concat]
    simp
    ext cs
    simp
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp at eq
        rw [eq] at ht
        exact ⟨[], hs, cs, ⟨ht, by simp⟩⟩
      case cons s_hd s_tl =>
        simp only [Language.nullify] at hs
        simp at hs
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp at eq
        rw [eq] at ht
        exact ⟨[], hs, (a ++ cs), ht, by simp⟩
      case cons s_hd s_tl s_ih =>
        simp only [Language.nullify] at hs
        simp at hs


lemma concat_derivative_and_nullify_wrt_str
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : Str α) :
  {s | a ++ s ∈ (concat L1 L2.nullify)} = concat (derivative L1 a) L2.nullify :=
  by
    simp only [derivative]
    simp only [concat]
    simp only [Language.nullify]
    simp
    ext cs
    simp
    constructor
    · intro a1
      obtain ⟨s, a2, t, ⟨a3, a4⟩, eq⟩ := a1
      cases s
      case nil =>
        simp at eq
        rw [eq] at a4
        simp at a4
        obtain ⟨a4_left, a4_right⟩ := a4
        rw [a4_left]
        rw [a4_right]
        simp
        exact ⟨a2, a3⟩
      case cons s_hd s_tl =>
        rw [a4] at eq
        simp at eq
        apply Exists.intro cs
        rw [← eq]
        constructor
        · exact a2
        · apply Exists.intro []
          simp
          exact a3
    · intro a1
      obtain ⟨s, a2, t, ⟨a3, a4⟩, eq⟩ := a1
      cases s
      case nil =>
        simp at eq
        simp at a2
        apply Exists.intro a
        constructor
        · exact a2
        · apply Exists.intro []
          rw [← eq]
          rw [a4]
          simp
          exact a3
      case cons s_hd s_tl s_ih =>
        rw [a4] at eq
        simp at eq
        rw [← eq]
        apply Exists.intro (a ++ s_tl :: s_ih)
        constructor
        · exact a2
        · apply Exists.intro []
          simp
          exact a3


lemma derivative_of_concat_wrt_char_aux
  {α : Type}
  [DecidableEq α]
  (L0 L2 : Language α)
  (a : α)
  (h1 : L0.nullify = ∅) :
  {t | a :: t ∈ concat L0 L2} = {t | ∃ t0 t2, a :: t0 ∈ L0 ∧ t2 ∈ L2 ∧ t0 ++ t2 = t} :=
  by
    simp only [Language.nullify] at h1
    simp at h1

    simp only [concat]
    simp
    ext cs
    constructor
    · simp
      intro s a1 t a2 a3
      cases s
      case nil =>
        contradiction
      case cons s_hd s_tl =>
        simp at a3
        cases a3
        case _ a3_left a3_right =>
          simp only [a3_left] at a1
          exact ⟨s_tl, a1, t, ⟨a2, a3_right⟩⟩
    · simp
      intro s a1 t a2 a3
      rw [← a3]
      exact ⟨a :: s, a1, t, a2, by simp⟩


-- 1.56
theorem derivative_of_concat_wrt_char
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : α) :
  derivative (concat L1 L2) [a] =
    (concat (derivative L1 [a]) L2) ∪ (concat L1.nullify (derivative L2 [a])) :=
  by
    have s1 : ∀ (L0 : Language α), L0.nullify = ∅ →
      derivative (concat (L1.nullify ∪ L0) L2) [a] =
        (concat L1.nullify (derivative L2 [a])) ∪ (concat (derivative L0 [a]) L2) :=
    by
      intro L0 a1
      calc
      derivative (concat (L1.nullify ∪ L0) L2) [a] =
        {s | a :: s ∈ concat (L1.nullify ∪ L0) L2} :=
      by
        simp only [derivative]
        rfl

      _ = {s | a :: s ∈ concat L1.nullify L2} ∪ {t | a :: t ∈ concat L0 L2} :=
      by
        obtain s3 := concat_distrib_union_right L1.nullify L0 L2
        simp only [s3]
        rfl

      _ = (concat L1.nullify (derivative L2 [a])) ∪ {t | ∃ t0 t2, a :: t0 ∈ L0 ∧ t2 ∈ L2 ∧ t0 ++ t2 = t} :=
      by
        obtain s3_1 := concat_nullify_and_derivative_wrt_char L1 L2 a
        simp only [s3_1]
        obtain s3_2 := derivative_of_concat_wrt_char_aux L0 L2 a a1
        simp only [s3_2]

      _ = (concat L1.nullify (derivative L2 [a])) ∪ concat {t0 | a :: t0 ∈ L0} L2 :=
      by
        simp only [concat]
        simp

      _ = (concat L1.nullify (derivative L2 [a])) ∪ (concat (derivative L0 [a]) L2) :=
      by
        simp only [derivative]
        rfl

    have s2 : ∀ (L0 : Language α), derivative (L1.nullify ∪ L0) [a] = derivative L0 [a] :=
    by
      intro L0
      simp only [derivative]
      simp only [Language.nullify]
      simp

    obtain s3 := lang_as_union_of_nullify_and_not_nullable L1
    cases s3
    case _ L0 a1 =>
      cases a1
      case _ a1_left a1_right =>
        specialize s1 L0 a1_left
        specialize s2 L0
        simp only [← a1_right] at s1
        simp only [← a1_right] at s2
        simp only [s2]
        simp only [s1]
        exact Set.union_comm (concat L1.nullify (derivative L2 [a])) (concat (derivative L0 [a]) L2)


theorem derivative_of_concat_wrt_str
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (s : Str α) :
  let B := { M | ∃ (u : Str α) (v : Str α), u ++ v = s ∧ v.length > 0 ∧ M = concat (derivative L1 u).nullify (derivative L2 v) }
  derivative (concat L1 L2) s = (concat (derivative L1 s) L2) ∪ ⋃₀ B :=
  by
    ext t
    simp [derivative, concat, Language.nullify]
    constructor
    · rintro ⟨u, hu, v, hv, eq⟩
      obtain ⟨w, rfl, rfl⟩ | ⟨w, rfl, rfl⟩ := List.append_eq_append_iff.1 eq
      · by_cases hw : w = []
        · subst w; simp at *
          exact .inl ⟨[], by simpa, _, hv, rfl⟩
        · simp only [List.length_pos]
          exact .inr ⟨_, ⟨u, _, rfl, hw, rfl⟩, _, ⟨hu, rfl⟩, _, hv, rfl⟩
      · exact .inl ⟨_, hu, _, hv, rfl⟩
    · rintro (⟨u, hu, v, hv, rfl⟩ | ⟨_, ⟨u, v, rfl, _, rfl⟩, _, ⟨hu, rfl⟩, _, hv, rfl⟩) <;>
        exact ⟨_, hu, _, hv, by simp⟩


-- 1.59
lemma derivative_of_exp_succ_wrt_char
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α)
  (k : ℕ) :
  derivative (exp L (k + 1)) [a] =
    concat (derivative L [a]) (exp L k) :=
  by
    induction k
    case zero =>
      simp
      simp only [exp]
      simp only [concat]
      simp
    case succ k ih =>
      rw [exp]
      simp only [concat_exp_comm]
      simp only [derivative_of_concat_wrt_char]
      simp only [Language.nullify]
      split_ifs
      case pos c1 =>
        simp only [concat_eps_left]
        simp only [ih]
        simp

        obtain s1 := eps_mem_exp_subset_exp_add_nat L k 1 c1

        exact concat_subset_left (derivative L [a]) (exp L k) (exp L (k + 1)) s1
      case neg c1 c2 =>
        simp only [concat]
        simp


lemma derivative_distrib_union_of_countable_wrt_char
  {α : Type}
  [DecidableEq α]
  (a : α)
  (f : ℕ → Language α) :
  ⋃ n, derivative (f n) [a] = derivative (⋃ n, f n) [a] :=
  by
    simp only [derivative]
    ext cs
    simp


lemma derivative_distrib_union_of_countable_wrt_str
  {α : Type}
  [DecidableEq α]
  (s : Str α)
  (f : ℕ → Language α) :
  ⋃ n, derivative (f n) s = derivative (⋃ n, f n) s :=
  by
    simp only [derivative]
    ext cs
    simp


lemma derivative_distrib_union_of_finset_wrt_char
  {α : Type}
  [DecidableEq α]
  {β : Type}
  (a : α)
  (Γ : Finset β)
  (f : β → Language α):
  ⋃ (x ∈ Γ), derivative (f x) [a] = derivative (⋃ (x ∈ Γ), f x) [a] :=
  by
    simp only [derivative]
    ext cs
    simp


lemma derivative_distrib_union_of_finset_wrt_str
  {α : Type}
  [DecidableEq α]
  {β : Type}
  (s : Str α)
  (Γ : Finset β)
  (f : β → Language α):
  ⋃ (x ∈ Γ), derivative (f x) s = derivative (⋃ (x ∈ Γ), f x) s :=
  by
    simp only [derivative]
    ext cs
    simp


-- 1.57
theorem derivative_of_kleene_closure_wrt_char
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α) :
  derivative (kleene_closure α L) [a] = concat (derivative L [a]) (kleene_closure α L) :=
  by
    conv => left; simp only [kleene_closure_eq_union_exp]
    simp only [← Set.union_iUnion_nat_succ (exp L)]
    simp only [derivative_of_union_wrt_char]
    simp only [exp_zero]
    simp only [derivative_of_eps_wrt_char]
    simp only [Set.empty_union]
    simp only [← derivative_distrib_union_of_countable_wrt_char]
    simp only [derivative_of_exp_succ_wrt_char]
    simp only [concat_distrib_countable_union_left]
    simp only [kleene_closure_eq_union_exp]


-- 1.58
theorem derivative_of_complement_wrt_char
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α) :
  derivative Lᶜ [a] = (derivative L [a])ᶜ := rfl
  -- Why is this proof so short?


theorem str_mem_lang_iff_eps_mem_derivative
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α) :
  s ∈ L ↔ [] ∈ derivative L s :=
  by
    simp only [derivative]
    simp


theorem str_mem_lang_iff_nullify_derivative_eq_eps
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α) :
  s ∈ L ↔ (derivative L s).nullify = {[]} :=
  by
    simp only [str_mem_lang_iff_eps_mem_derivative L]
    simp only [Language.nullify]

    split_ifs
    case pos c1 =>
      simp
      exact c1
    case neg c1 =>
      simp only [c1]
      simp
      obtain s1 := Set.singleton_ne_empty []
      exact id (Ne.symm s1)


theorem lang_eq_union_nullify_union_concat_char_derivative_wrt_char
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  L = L.nullify ∪ ⋃ (a : α), concat {[a]} (derivative L [a]) :=
  by
    ext cs
    constructor
    · intro a1
      cases cs
      case _ =>
        simp
        left
        simp only [Language.nullify]
        simp only [a1]
        simp
      case _ hd tl =>
        simp
        right
        apply Exists.intro hd
        simp only [concat]
        simp
        simp only [derivative]
        simp
        exact a1
    · intro a1
      simp at a1
      cases a1
      case _ a1_left =>
        simp only [Language.nullify] at a1_left
        simp at a1_left
        cases a1_left
        case _ a1_left_left a1_left_right =>
          simp only [a1_left_right]
          exact a1_left_left
      case _ a1_right =>
        obtain ⟨i, a2⟩ := a1_right
        simp only [concat] at a2
        simp only [derivative] at a2
        simp at a2
        obtain ⟨t, ⟨a3_left, a3_right⟩⟩ := a2
        rw [← a3_right]
        exact a3_left


lemma derivative_of_nullify_wrt_char
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α) :
  derivative (L.nullify) [a] = ∅ :=
  by
    simp only [derivative]
    simp
    simp only [Language.nullify]
    simp


lemma concat_derivative_kleene_closure_subset
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a b : Str α)
  (h1 : b ∈ L) :
  concat (derivative L a) (kleene_closure α L) ⊆
    concat (derivative L b).nullify (derivative (kleene_closure α L) a) :=
  by
    simp only [Set.subset_def]
    intro x a1
    simp only [concat] at a1
    simp at a1
    obtain ⟨s, hs, t, ht, eq⟩ := a1
    rw [← eq]
    simp only [concat]
    simp
    apply Exists.intro []
    simp
    simp only [derivative]
    simp only [Language.nullify]
    simp
    constructor
    · exact h1
    · simp only [String.str_append_assoc]
      apply append_kleene_closure_closed
      · exact mem_language_mem_kleene_closure L (a ++ s) hs
      · exact ht


noncomputable def foo'
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α) :
  List (List α) :=
  match s with
  | [] => []
  | hd :: tl =>
    open Classical in
    let l1 :=
      tl.tails.filter fun s => ¬ s = [] ∧ [] ∈ derivative L (hd :: tl.take (tl.length - s.length))
    have IH (v : List α) (h : v.IsSuffix tl) :=
      have : v.length ≤ tl.length := h.length_le
      foo' L v
    let l2 := l1.attach.bind fun ⟨v, h⟩ => by
      simp [l1, List.mem_filter] at h
      exact IH v h.1
    (hd :: tl) :: l2
termination_by s.length


lemma derivative_of_kleene_closure_wrt_str
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α)
  (h1 : ¬ s = []) :
  derivative (kleene_closure α L) s =
    ⋃ t ∈ foo' L s, concat (derivative L t) (kleene_closure α L) :=
  by
    cases e : s
    case nil =>
      contradiction
    case cons hd tl =>
      have IH : ∀ (v : List α), v.IsSuffix tl → ¬ v = [] → derivative (kleene_closure α L) v = ⋃ t ∈ foo' L v, concat (derivative L t) (kleene_closure α L) :=
      by
        intro v h
        have : v.length < s.length :=
        by
          rw [e]
          simp
          apply Nat.lt_succ_of_le
          exact List.IsSuffix.length_le h
        exact derivative_of_kleene_closure_wrt_str L v

      rw [derivative_wrt_cons]
      simp only [derivative_of_kleene_closure_wrt_char]
      simp only [derivative_of_concat_wrt_str]
      simp only [← derivative_wrt_append]
      simp only [List.singleton_append]

      simp only [foo']

      simp
      congr! 1
      ext cs

      simp only [List.length_pos]
      simp

      constructor
      · intro a1
        obtain ⟨M, ⟨u, v, a2, a3, a4⟩, a5⟩ := a1

        have s1 : v.IsSuffix tl :=
        by
          simp only [List.IsSuffix]
          apply Exists.intro u
          exact a2

        specialize IH v s1 a3

        rw [a4] at a5
        clear a4
        simp only [mem_concat_nullify_left_iff] at a5
        obtain ⟨a6, a7⟩ := a5

        apply Exists.intro v
        constructor
        · constructor
          · exact s1
          · constructor
            · exact a3
            · rw [← a2]
              simp
              exact a6
        · rw [IH] at a7
          simp at a7
          exact a7
      · intro a1
        obtain ⟨i, ⟨a2, a3, a4⟩, j, a5, a6⟩ := a1

        simp only [derivative] at a4
        simp at a4

        specialize IH i a2 a3

        simp only [List.IsSuffix] at a2
        obtain ⟨t, ht⟩ := a2

        rw [← ht] at a4
        simp at a4

        apply Exists.intro (derivative (kleene_closure α L) i)
        constructor
        · apply Exists.intro t
          apply Exists.intro i
          constructor
          · exact ht
          · constructor
            · exact a3
            · simp only [Language.nullify]
              split_ifs
              case pos c1 =>
                simp only [concat_eps_left]
              case neg c1 =>
                simp only [derivative] at c1
                simp at c1
                contradiction
        · rw [IH]
          simp
          apply Exists.intro j
          tauto
termination_by s.length
