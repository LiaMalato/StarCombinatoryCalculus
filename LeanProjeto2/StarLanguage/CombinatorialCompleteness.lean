import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.Axioms
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.SHFunctInterp
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Batteries

open LFormula
open Term
open Formula
open Set
open Batteries




-- ---------------------------------------------------------------------------------
-- ---------------------------------------------------------------------------------
-- ---------------------------------------------------------------------------------
-- ---------------------------------------------------------------------------------

/- ----------------------------------------
      Lambda abstraction through terms
-/ ----------------------------------------

inductive lambda : Type
| la (s : String) (body : Term): lambda

def lambda.to_term : lambda → Term
| .la _ Π₁ => Π₁·Π₁
| .la _ Σ₁ => Π₁·Σ₁
| .la _ ind_⋃₁ => Π₁·ind_⋃₁
| .la _ ∪₁ => Π₁·∪₁
| .la _ 𝔰₁ => Π₁·𝔰₁
| .la _ (lcons k) => Π₁·(lcons k)
| .la _ (lfun f) => Π₁·(lfun f)
| .la x (var y) => if x=y then ((Σ₁·Π₁)·Π₁) else (Π₁·(var y))
| .la x (t·s) => ((Σ₁·(lambda.la x t).to_term)·(lambda.la x s).to_term)

def testu := lambda.la "y" .pi
def testu2 := lambda.la "x" (lambda.la "y" .pi).to_term
def testu3 := lambda.la "x" (lambda.la "y" ((lambda.la "z" .pi).to_term)).to_term
#eval testu.to_term
#eval testu2.to_term
#eval testu3.to_term

def lambdas_no (fs: List String) (bodies: List Term) : List lambda :=
  (fs.zip bodies).map ( fun (f, b) => lambda.la f b)

def lambdas : List String → Term → Term
| [], body => body                                         -- sem variáveis, não acontece nada
| f :: fs, body => (lambda.la f (lambdas fs body)).to_term -- recursively nesting lambda abstractions

notation "λ₁₁" => lambdas

#eval λ₁₁ ["x", "y"] .pi
#eval λ₁₁ ["x"] .pi

-- Define lambdas_tuple
def lambdas_tuple : List String → List Term → List Term
| vars, ts => ts.map (λ t => lambdas vars t)
  -- Apply lambdas to each term in the list ts using the list of variables vars

notation "λ₁" => lambdas_tuple

-- EXEMPLO:
#eval λ₁ ["x1", "x2"] [.pi, .sigma, .sing]
#eval λ₁ ["x", "y"] [.pi, .sigma]


-- ------------------------------------------------------------

/- ----------------------------------------
      Conversions
-/ ----------------------------------------

open lambda

#eval ((la "x" Π₁).to_term)                     -- a tirar

inductive conversion : Type                     -- a tirar
| c1 (t₁ t₂ : Term) : conversion
| c2 (t₁ t₂ t₃ : Term) : conversion
| c3 (t₁ t₂ : Term) : conversion
| c4 (t₁ t₂ t₃ : Term) : conversion

def conversion.to_Term : conversion → Term      -- a tirar
| .c1 t₁ t₂ => t₁
| .c2 t₁ t₂ t₃ => ((t₁·t₃)·(t₂·t₃))
| .c3 t₁ t₂ => (t₂·t₁)
| .c4 t₁ t₂ t₃ => (∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)

open conversion                                 -- a tirar

def Conv1 (t₁ t₂ : Term) := (((Π₁·t₁)·t₂) = t₁)
def Conv2 (t₁ t₂ t₃ : Term) := ((((Σ₁·t₁)·t₂)·t₃) = ((t₁·t₃)·(t₂·t₃)))
def Conv3 (t₁ t₂ : Term) := (((ind_⋃₁·(𝔰₁·t₁))·t₂) = (t₂·t₁))
def Conv4 (t₁ t₂ t₃ : Term) := (((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) = ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)))

lemma Conv1_l (t₁ t₂ : Term) : (((Π₁·t₁)·t₂) = t₁) := by sorry
lemma Conv2_l (t₁ t₂ t₃ : Term) : ((((Σ₁·t₁)·t₂)·t₃) = ((t₁·t₃)·(t₂·t₃))) := by sorry
lemma Conv3_l (t₁ t₂ : Term) : (((ind_⋃₁·(𝔰₁·t₁))·t₂) = (t₂·t₁)) := by sorry
lemma Conv4_l (t₁ t₂ t₃ : Term) : (((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) = ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃))) := by sorry


-- (((ind_⋃₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁))
--(((ind_⋃₁·((∪₁·(var x₁))·(var x₂)))·(var x₃)) =₁ ((∪₁·((ind_⋃₁·(var x₁))·(var x₃)))·((ind_⋃₁·(var x₂))·(var x₃))))

-- Para exemplos
def CC_var_eq : Term := ((Σ₁·Π₁)·Π₁)
def CC_var_dif : Term := ((Σ₁·Π₁)·Π₁)
def CC_const : Term := ((Σ₁·Π₁)·Π₁)

/--/
lemma cenass (x : String) (s : Term) (c : LTerm) : ((lcons c)=((lcons c).subst ([x]⟹[s]))) :=
by
  rw [Term.subst]
  rw [remove_non_l_terms]
  sorry
-/

-- Igualdades entre termos são igualdades  -- TBD: seria necessário definir substituição de termos por termos
lemma eq_are_eq {Γ : Set Formula} (t q : Term) (h: Γ ⊢ t=₁q): t=q := by sorry

-- OLD (a tirar)
theorem combinatorial_completeness (x : String) : ∀(t:Term), ∃(q:Term), ∀(s:Term),
  (Γ ⊢ ((q·s) =₁ (t.subst ([x] ⟹ [s])))) :=
by
  intro t
  cases t with
  | lcons _ =>
      rename_i c
      existsi ((la x (lcons c)).to_term)    --existsi Π₁·(lcons c)
      intro s
      rw [to_term]
      have H1 := Conv1_l (lcons c) s
      rw [H1]                         -- precisamos de:    Γ ⊢ lcons c=₁(lcons c).subst ([x]⟹[s])
      rw [Term.subst]
      --rw [remove_non_l_terms]
      sorry
  | lfun _ => sorry
  | pi =>
      existsi ((la x Π₁).to_term)     -- em vez de:  existsi Π₁·Π₁
      intro s
      rw [to_term]
      have H1 := Conv1_l Π₁ s
      rw [H1]
      rw [Term.subst]                  -- precisamos de:   Γ ⊢ Π₁=₁Π₁
      --have H2 := ProvableFrom.subs ( Π₁ =₁ Π₁ )
      sorry
  | sigma =>
      existsi ((la x Σ₁).to_term)      --existsi Π₁·Σ₁
      intro s
      rw [to_term]
      have H1 := Conv1_l Σ₁ s
      rw [H1]
      rw [Term.subst]                   -- precisamos de:   Γ ⊢ Σ₁=₁Σ₁
      sorry
  | sing =>
      existsi ((la x 𝔰₁).to_term)       --existsi Π₁·𝔰₁
      intro s
      rw [to_term]
      have H1 := Conv1_l 𝔰₁ s
      rw [H1]
      rw [Term.subst]                   -- precisamos de:   Γ ⊢ 𝔰₁=₁𝔰₁
      sorry
  | bUnion =>
      existsi ((la x ∪₁).to_term)       --existsi Π₁·𝔰₁
      intro s
      rw [to_term]
      have H1 := Conv1_l bUnion s
      rw [H1]
      rw [Term.subst]       -- precisamos de:   Γ ⊢ ∪₁=₁∪₁
      sorry
  | iUnion =>
      existsi ((la x ind_⋃₁).to_term)       --existsi Π₁·𝔰₁
      intro s
      rw [to_term]
      have H1 := Conv1_l iUnion s
      rw [H1]
      rw [Term.subst]       -- precisamos de:   Γ ⊢ ind_⋃₁=₁ind_⋃₁
      sorry
  | var y =>
      by_cases h: x = y
      . existsi ((la x (var y)).to_term)       --existsi Π₁·𝔰₁
        intro s
        rw [to_term]
        simp [h]
        --existsi ((Σ₁·Π₁)·Π₁)
        --intro s
        have H1 := Conv2_l Π₁ Π₁ s
        rw [H1]
        have H2 := Conv1_l s (Π₁·s)
        rw [H2]
        unfold Term.subst           -- ⊢ Γ ⊢ s=₁([y]⟹[s]).findD y (var y)
        sorry
      . existsi ((la x (var y)).to_term)
        --existsi (Π₁·(var y))
        intro s
        rw [to_term]
        simp [h]
        have H1 := Conv1_l (var y) s
        rw [H1]
        sorry               -- precisamos de:    ⊢ Γ ⊢ var y=₁(var y).subst ([x]⟹[s])
  | app t₁ t₂ => -- BY INDUCTION
      --existsi ((la x (t₁·t₂)).to_term)
      --intro s
      --rw [to_term]
      sorry


-- OLD (a tirar)
theorem combinatorial_completeness2 (x : String) : ∀(t:Term), ∃(q:Term), ∀(s:Term),
  (Γ ⊢ ((q·s) =₁ (t.subst ([x] ⟹ [s])))) :=
by
  intro t
  induction t with
  | lcons _ => sorry
  | lfun _ => sorry
  | pi => sorry
  | sigma => sorry
  | sing =>
        existsi ((la x 𝔰₁).to_term)       --existsi Π₁·𝔰₁
        intro s
        rw [to_term]
        rw [Term.subst]
        exact AxC₁_term 𝔰₁ s
        --exact ProvableFrom.AxC₁
  | bUnion => sorry
  | iUnion => sorry
  | var y =>
      by_cases h: x = y
      . existsi ((la x (var y)).to_term)   --existsi Π₁·𝔰₁
        intro s
        rw [to_term]
        simp [h]
        --existsi ((Σ₁·Π₁)·Π₁)
        --intro s
        have H1 := Conv2_l Π₁ Π₁ s
        rw [H1]
        have H2 := Conv1_l s (Π₁·s)
        rw [H2]
        unfold Term.subst           -- ⊢ Γ ⊢ s=₁([y]⟹[s]).findD y (var y)
        sorry
      . existsi ((la x (var y)).to_term)
        --existsi (Π₁·(var y))
        intro s
        rw [to_term]
        simp [h]
        have H1 := Conv1_l (var y) s
        rw [H1]
        rw [Term.subst]
        sorry
  | app _ _ _ _ =>
        rename_i t₁ t₂ ht₁ ht₂
        existsi ((la x (t₁·t₂)).to_term)
        intro s
        rcases ht₁ with ⟨q₁, hq₁⟩
        rcases ht₂ with ⟨q₂, hq₂⟩
        have h₁ := hq₁ s
        have h₂ := hq₂ s
        rw [to_term]
        have H1 := Conv2_l ((la x t₁).to_term) ((la x t₂).to_term) s
        rw [H1]
        rw [Term.subst]
        have H1 := eq_are_eq (q₁·s) (t₁.subst ([x]⟹[s])) h₁
        rw [← H1]
        have H2 := eq_are_eq (q₂·s) (t₂.subst ([x]⟹[s])) h₂
        rw [← H2]
        sorry
        --rw [h₁, h₂]

lemma eq_to_subst :
  Γ ⊢ (t₁ =₁ t₂) →
  Γ ⊢ t →
  Γ ⊢ (t.term_subst t₁ t₂)
  := by sorry

lemma helper_cc1 : (([x]⟹[s]).findD c (lcons c)) = (lcons c) := by sorry
lemma helper_cc2 : (([x]⟹[s]).findD f (lfun f)) = (lfun f) := by sorry
lemma helper_cc3 : ((HashMap.ofList [(x, s)]).findD y (var y)) = (var y) := by sorry
lemma helper_cc4 (y:String) (s d :Term): ((HashMap.ofList [(y, s)]).findD y d) = s := by sorry
lemma helper_t {t₁ t₂ t₃ : Term} : (Γ ⊢ t₁ =₁ t₂) → (Γ ⊢ t₂ =₁ t₃) → (Γ ⊢ t₁ =₁ t₃) := by sorry
lemma helper_subst_l {t₁ t₂ t₃ t₂' : Term} : (Γ ⊢ t₁ =₁ (t₂·t₃)) → (Γ ⊢ t₂ =₁ t₂') → (Γ ⊢ t₁ =₁ (t₂'·t₃)) := by sorry
lemma helper_subst_r {t₁ t₂ t₃ t₃' : Term} : (Γ ⊢ t₁ =₁ (t₂·t₃)) → (Γ ⊢ t₃ =₁ t₃') → (Γ ⊢ t₁ =₁ (t₂·t₃')) := by sorry


-- good version
theorem CombinatorialCompleteness {x₁ x₂ x₃ : String} (x:String) (s:Term):
  ∀(t:Term),
  (Γ ⊢ ((((la x t).to_term)·s) =₁ (t.subst ([x] ⟹ [s])))) :=
by
  intro t
  induction t with
  | lcons c =>
      rw [to_term, Term.subst]
      rw [helper_cc1]
      exact AxC₁_term (lcons c) s
  | lfun f =>
      rw [to_term, Term.subst]
      rw [helper_cc2]
      exact AxC₁_term (lfun f) s
  | pi =>
      rw [to_term, Term.subst]
      exact AxC₁_term Π₁ s
  | sigma =>
      rw [to_term, Term.subst]
      exact AxC₁_term Σ₁ s
  | sing =>
      rw [to_term, Term.subst]
      exact AxC₁_term 𝔰₁ s
  | bUnion =>
      rw [to_term, Term.subst]
      exact AxC₁_term ∪₁ s
  | iUnion =>
      rw [to_term, Term.subst]
      exact AxC₁_term ind_⋃₁ s
  | var y =>
      by_cases h: x = y
      . rw [to_term]
        simp [h]
        rw [Term.subst]           --  ⊢   Γ ⊢ (((Σ₁·Π₁)·Π₁)·s)=₁([y]⟹[s]).findD y (var y)
        rw [helper_cc4]
        have H1 := @AxC₂_term_l Γ x₁ x₂ x₃ Π₁ Π₁ s
        have H2 := @AxC₁_term_l Γ x₁ x₂ s (Π₁·s)
        exact helper_t H1 H2    -- permitiu aplicar AxC2 e depois AxC1
      . rw [to_term]
        simp [h]
        rw [Term.subst]           --  ⊢   Γ ⊢ ((Π₁·var y)·s)=₁([x]⟹[s]).findD y (var y)
        rw [helper_cc3]
        exact AxC₁_term (var y) s
  | app t₁ t₂ ht₁ ht₂ =>
      rw [to_term]
      rw [Term.subst]
      have H1 := @AxC₂_term_l Γ x₁ x₂ x₃ ((la x t₁).to_term) ((la x t₂).to_term) s
      have Hr := @helper_subst_l Γ (((Σ₁·(la x t₁).to_term)·(la x t₂).to_term)·s) (((la x t₁).to_term·s)) ((la x t₂).to_term·s) (t₁.subst ([x]⟹[s])) H1 ht₁
      exact @helper_subst_r Γ (((Σ₁·(la x t₁).to_term)·(la x t₂).to_term)·s) (t₁.subst ([x]⟹[s])) ((la x t₂).to_term·s) (t₂.subst ([x]⟹[s])) Hr ht₂
