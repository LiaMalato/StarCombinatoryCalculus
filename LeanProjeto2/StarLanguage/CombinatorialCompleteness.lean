import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.Axioms
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.SHFunctInterp
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Batteries

open LFormula
open Term
open Formula
open Set
open Batteries

-- -------------------------------------------------------------
-- -------------------------------------------------------------
--         STAR LANGUAGE - COMBINATORIAL COMPLETENESS
--    (SECTION 1.2.4: The Combinatorial Completeness Theorem)
-- -------------------------------------------------------------
-- -------------------------------------------------------------

/- FILE DESCRIPTION:
In this file we discuss the Combinatorial Completeness Theorem.
We begin by defining lambda abstractions to then state and prove
the theorem. The file corresponds to pages 19 to 21.
-/

-- -------------------------------------------------------------
-- DEFINITION 1.11 (p.21):
-- The term q for the Combinatorial Completeness Theorem
-- -------------------------------------------------------------

/-
To define the term q we first define lambda abstraction.
-/

-- Construction of the lambda notation for the proof
inductive lambda
| la (x : String) (t : Term): lambda          -- represents the lambda notation

open lambda

-- Construction of the term q for the proof of the Completeness Theorem
def lambda.to_term : lambda → Term
| la _ Π₁         => Π₁·Π₁                                        -- λx.Π = Π·Π
| la _ Σ₁         => Π₁·Σ₁
| la _ i∪₁        => Π₁·i∪₁
| la _ ∪₁         => Π₁·∪₁
| la _ 𝔰₁         => Π₁·𝔰₁
| la _ (lcons k)  => Π₁·(lcons k)
| la _ (lfun f)   => Π₁·(lfun f)
| la x (var y)    => if x=y then ((Σ₁·Π₁)·Π₁)                     -- λx.x = (Σ·Π)·Π
                     else (Π₁·(var y))                            -- λx.y = Π·y
| la x (t·s)      => ((Σ₁·(la x t).to_term)·(la x s).to_term)     -- λx.(t₁·t₂) = Σ·(λx.t₁)·(λx.t₂)

def testu := lambda.la "y" .pi
def testu2 := lambda.la "x" (lambda.la "y" .pi).to_term
def testu3 := lambda.la "x" (lambda.la "y" ((lambda.la "z" .pi).to_term)).to_term
#eval testu.to_term
#eval testu2.to_term
#eval testu3.to_term

def lambdas_no (fs: List String) (bodies: List Term) : List lambda :=
  (fs.zip bodies).map ( fun (f, b) => lambda.la f b)

def lambdas : List String → Term → Term
| [], body => body                                           -- without variables nothing happens
| f :: fs, body => (lambda.la f (lambdas fs body)).to_term   -- we recursively nest the lambda abstractions

-- NOTATION:
notation "λ₁₁" => lambdas

#eval λ₁₁ ["x", "y"] .pi          -- λx,y.Π
#eval λ₁₁ ["x"] .pi               -- λx.Π     (the new definition works with single variables)

-- DEFINITION: lambdas_tuple
def lambdas_tuple : List String → List Term → List Term
| vars, ts => ts.map (λ t => lambdas vars t)
  -- Apply lambdas to each term in the list ts using the list of variables vars

notation "λ₁" => lambdas_tuple

-- EXAMPLE:
#eval λ₁ ["x1", "x2"] [.pi, .sigma, .sing]
#eval λ₁ ["x", "y"] [.pi, .sigma]


-- ---------------------------------------
-- AUXILLIARY LEMMAS
-- ---------------------------------------

-- Equalities between terms are true equalities
lemma eq_are_eq {Γ : Set Formula} (t q : Term) (h: Γ ⊢ t=₁q): t=q := by sorry
lemma eq_are_eq_tuple {Γ : Set Formula} {t q : List Term} (h: Γ ⊢ t =_t q): t=q := by sorry

lemma eq_to_subst :
  Γ ⊢ (t₁ =₁ t₂) →
  Γ ⊢ t →
  Γ ⊢ (t.term_subst t₁ t₂)
  := by sorry

-- Technicalities
lemma helper_cc1 : (([x]⟹[s]).findD c (lcons c)) = (lcons c) := by sorry
lemma helper_cc2 : (([x]⟹[s]).findD f (lfun f)) = (lfun f) := by sorry
lemma helper_cc3 (x y : String) (s : Term): ((HashMap.ofList [(x, s)]).findD y (var y)) = (var y) := by sorry
lemma helper_cc4 (y:String) (s t :Term): ((HashMap.ofList [(y, s)]).findD y t) = s := by sorry
lemma eq_trans {t₁ t₂ t₃ : Term} : (Γ ⊢ t₁ =₁ t₂) → (Γ ⊢ t₂ =₁ t₃) → (Γ ⊢ t₁ =₁ t₃) := by sorry
lemma helper_subst_l {t₁ t₂ t₃ t₂' : Term} : (Γ ⊢ t₁ =₁ (t₂·t₃)) → (Γ ⊢ t₂ =₁ t₂') → (Γ ⊢ t₁ =₁ (t₂'·t₃)) := by sorry
lemma helper_subst_r {t₁ t₂ t₃ t₃' : Term} : (Γ ⊢ t₁ =₁ (t₂·t₃)) → (Γ ⊢ t₃ =₁ t₃') → (Γ ⊢ t₁ =₁ (t₂·t₃')) := by sorry


-- -------------------------------------------------------------
-- THEOREM 1.1 (p.20):
-- The Combinatorial Completeness Theorem
-- -------------------------------------------------------------

-- Proof of the Combinatorial Completeness Theorem
theorem CombinatorialCompleteness {x₁ x₂ x₃ : String} (x:String) (s:Term):
  ∀(t:Term),
  Γ ⊢ ((((la x t).to_term)·s) =₁ (t.subst ([x] ⟹ [s]))) :=
by
  intro t                             -- Let t be a term.
  induction t with                    -- We will prove the theorem by induction on t.
  | lcons c =>
      rw [to_term, Term.subst]
      rw [helper_cc1]
      exact AxC₁_term (lcons c) s
  | lfun f =>
      rw [to_term, Term.subst]
      rw [helper_cc2]
      exact AxC₁_term (lfun f) s
  | pi =>                             -- Case 1: when t is the combinator Π
      rw [to_term]                       -- simplifies ((la x Π₁).to_term)·s to (Π₁·Π₁)·s
      rw [Term.subst]                    -- simplifies Π₁.subst ([x]⟹[s]) to Π₁
      exact AxC₁_term Π₁ s               -- closes the goal by using AxC₁ for terms
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
      exact AxC₁_term i∪₁ s
  | var y =>                          -- Case 2: when t is a variable y
      by_cases h: x = y               -- breaks the proof into two subgoals: when x=y and ¬(x=y)
      . rw [to_term]                     -- a) when t is the variable x, i.e. x=y
        simp [h]
        rw [Term.subst]                  --  ⊢   Γ ⊢ (((Σ₁·Π₁)·Π₁)·s)=₁([y]⟹[s]).findD y (var y)
        rw [helper_cc4]
        have H1 := @AxC₂_term Γ Π₁ Π₁ s     -- introduction of a new hypothesis H1
        have H2 := @AxC₁_term Γ s (Π₁·s)    -- introduction of a new hypothesis H2
        exact eq_trans H1 H2                -- applies AxC2 followed by AxC1 to close the goal
      . rw [to_term]                     -- b) when t is the variable x, i.e. x=y
        simp [h]
        rw [Term.subst]                  --  ⊢   Γ ⊢ ((Π₁·var y)·s)=₁([x]⟹[s]).findD y (var y)
        rw [helper_cc3]
        exact AxC₁_term (var y) s
  | app t₁ t₂ ht₁ ht₂ =>
      rw [to_term]
      rw [Term.subst]
      have H1 := @AxC₂_term_l Γ x₁ x₂ x₃ ((la x t₁).to_term) ((la x t₂).to_term) s
      have Hr := @helper_subst_l Γ (((Σ₁·(la x t₁).to_term)·(la x t₂).to_term)·s) (((la x t₁).to_term·s)) ((la x t₂).to_term·s) (t₁.subst ([x]⟹[s])) H1 ht₁
      exact @helper_subst_r Γ (((Σ₁·(la x t₁).to_term)·(la x t₂).to_term)·s) (t₁.subst ([x]⟹[s])) ((la x t₂).to_term·s) (t₂.subst ([x]⟹[s])) Hr ht₂


-- -------------------------------------------------------------
-- THEOREM: The Combinatorial Completeness Theorem for tuples
-- -------------------------------------------------------------

theorem CombinatorialCompleteness_tuples (x: List String) (s: List Term):
  ∀(t:List Term),
  (Γ ⊢ (((λ₁ x t) ⊙ s) =_t (t.subst (x ⟹ s)))) := by sorry
