import Language.Regular


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


inductive RegExp (α : Type) : Type
  | char : α → RegExp α
  | epsilon : RegExp α
  | zero : RegExp α
  | union : RegExp α → RegExp α → RegExp α
  | concat : RegExp α → RegExp α → RegExp α
  | kleene_closure : RegExp α → RegExp α
  deriving Inhabited, DecidableEq

compile_inductive% RegExp


namespace RegExp


def LanguageOf
  {α : Type} :
  RegExp α → Language α
  | char c => {[c]}
  | epsilon => {[]}
  | zero => ∅
  | union R S => R.LanguageOf ∪ S.LanguageOf
  | concat R S => Language.concat R.LanguageOf S.LanguageOf
  | kleene_closure R => Language.kleene_closure α R.LanguageOf


example
  {α : Type}
  (RE : RegExp α) :
  Language.IsRegLang RE.LanguageOf :=
  by
    induction RE
    case char c =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.char c
    case epsilon =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.epsilon
    case zero =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.zero
    case union R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.union R.LanguageOf S.LanguageOf R_ih S_ih
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.concat R.LanguageOf S.LanguageOf R_ih S_ih
    case kleene_closure R R_ih =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.kleene_closure R.LanguageOf R_ih
