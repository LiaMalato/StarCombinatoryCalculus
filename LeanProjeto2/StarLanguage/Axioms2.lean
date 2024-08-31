-- -------------------------------------------------------------
--            STAR LANGUAGE - AXIOMS (new)
--          Versão adaptada de Patrick Massot
-- -------------------------------------------------------------

import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.Syntax
import MathLib.Tactic

open FOLang
open LFormula
open Term
open Formula
open Set

-- --------------------------------------
-- --------------------------------------
-- ------------- AXIOMS -----------------
-- --------------------------------------
-- --------------------------------------


namespace Axioms

def AxiomE1 (t:Term) : Formula :=                                    t=₁t
def AxiomE2 (t₁ t₂ :Term) (A : Formula) (hA : isBase A) : Formula := (t₁=₁t₂) ∧₁ (A →₁ A)     -- TBD: falta substituição aqui
def AxiomU (x : String) (t : Term) (A : Formula) : Formula :=        (b∀₁₁ x t A) ↔₁ (∀₁₁ x (((var x) ∈₁ t) →₁ A))
def AxiomC1 (t₁ t₂ : Term) : Formula :=                              ((Π₁·t₁)·t₂) =₁ t₁
def AxiomC2 (t₁ t₂ t₃ : Term) : Formula :=                           (((Σ₁·t₁)·t₂)·t₃) =₁ ((t₁·t₃)·(t₂·t₃))
def AxiomP1 (t₁ t₂ : Term) : Formula :=                              ((ind_⋃₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁)
def AxiomP2 (t₁ t₂ t₃ : Term) : Formula :=                           ((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) =₁ ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃))
def AxiomS1 (t₁ t₂ : Term) : Formula :=                              (t₁ ∈₁ (𝔰₁·t₂)) ↔₁ (t₁ =₁ t₂)
def AxiomS2 (t₁ t₂ t₃ : Term) : Formula :=                           (t₁ ∈₁ ((∪₁·t₂)·t₃) ) ↔₁ ((t₁ ∈₁ t₂) ∨₁ (t₁ ∈₁ t₃))
def AxiomS3 (a f b : Term) (x : String) : Formula :=                 (b ∈₁ ((ind_⋃₁·a)·f)) ↔₁ (b∃₁₁ x a (b ∈₁ (f·(var x))))
-- TBD: FALTA AXS4

end Axioms



def Axreflexivity (x : String) : Formula := (Term.var x) =₁ (Term.var x)


section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` is the predicate that there is a proof tree with conclusion `A` with assumptions from
  `Γ`. This is a typical list of rules for natural deduction with classical logic. -/


-- Reflexivity axiom

open Axioms

inductive ProvableFrom : Set Formula → Formula → Prop
| ax    : ∀ {Γ A},   A ∈ Γ   → Γ ⊢ A
| impI  : ∀ {Γ A B},  insert A Γ ⊢ B                 → Γ ⊢ A →₁ B
| impE  : ∀ {Γ A B},           Γ ⊢ (A →₁ B) → Γ ⊢ A  → Γ ⊢ B
| andI  : ∀ {Γ A B},           Γ ⊢ A        → Γ ⊢ B  → Γ ⊢ A ∧₁ B
| andE1 : ∀ {Γ A B},           Γ ⊢ (A ∧₁ B)          → Γ ⊢ A
| andE2 : ∀ {Γ A B},           Γ ⊢ (A ∧₁ B)          → Γ ⊢ B
| orI1  : ∀ {Γ A B},           Γ ⊢ A                → Γ ⊢ (A ∨₁ B)
| orI2  : ∀ {Γ A B},           Γ ⊢ B                → Γ ⊢ (A ∨₁ B)
| orE   : ∀ {Γ A B C}, Γ ⊢ (A ∨₁ B) → insert A Γ ⊢ C → insert B Γ ⊢ C → Γ ⊢ C

-- TWO AXIOM SCHEMA:
| exMid : ∀ {A},               ∅ ⊢ ((¬₁A)∨₁A)
--| subs : ∀ {A},              ∅ ⊢ ((∀₁ x A) →₁ A)     -- TBD: falta substituição aqui

-- FIVE RULES:
| exp :     ∀ {A B},          ∅ ⊢ A             →   ∅ ⊢ (B∨₁A)
| contrad : ∀ {A},            ∅ ⊢ (A∨₁A)        →   ∅ ⊢ A
| assoc :   ∀ {A B C},        ∅ ⊢ (A∨₁(B∨₁C))   →   ∅ ⊢ ((A∨₁B)∨₁C)
| cut :     ∀ {A B C},        ∅ ⊢ (A∨₁B)        →   ∅ ⊢ ((¬₁A)∨₁C)    →   ∅ ⊢ (B∨₁C)
--| forallInt : ∀ {A B},      ∅ ⊢ (A∨₁B)    →   ∅ ⊢ ((∀₁ x A)∨₁B)   -- TBD: falta substituição aqui

-- AXIOMS:
| AxE₁ (t:Term) :                               ∅ ⊢ (t=₁t)
| AxE₂ (t₁ t₂ :Term) (hA : isBase A) :          ∅ ⊢ ((t₁=₁t₂) ∧₁ (A →₁ A))     -- TBD: falta substituição aqui
| AxU (x : String) (t : Term) (A : Formula) :   ∅ ⊢ ((b∀₁₁ x t A) ↔₁ (∀₁₁ x (((var x) ∈₁ t) →₁ A)))
| AxC₁ (t₁ t₂ : Term) :                         ∅ ⊢ (((Π₁·t₁)·t₂) =₁ t₁)
| AxC₂ (t₁ t₂ t₃ : Term) :                      ∅ ⊢ ((((Σ₁·t₁)·t₂)·t₃) =₁ ((t₁·t₃)·(t₂·t₃)))
| AxP₁ (t₁ t₂ : Term) :                         ∅ ⊢ (((ind_⋃₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁))
| AxP₂ (t₁ t₂ t₃ : Term) :                      ∅ ⊢ (((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) =₁ ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)))
| AxS₁ (t₁ t₂ : Term) :                         ∅ ⊢ ((t₁ ∈₁ (𝔰₁·t₂)) ↔₁ (t₁ =₁ t₂))
| AxS₂ (t₁ t₂ t₃ : Term) :                      ∅ ⊢ ((t₁ ∈₁ ((∪₁·t₂)·t₃) ) ↔₁ ((t₁ ∈₁ t₂) ∨₁ (t₁ ∈₁ t₃)))
| AxS₃ (a f b : Term) :                         ∅ ⊢ ((b ∈₁ ((ind_⋃₁·a)·f)) ↔₁ (b∃₁₁ x a (b ∈₁ (f·(var x)))))
-- TBD: FALTA AXS4
| AxE1 (t:Term):          ∅ ⊢ AxiomE1 t
| AxE2:          ∅ ⊢ AxiomE2 t₁ t₂ A hA
| AxUu:          ∅ ⊢ AxiomU x t A
| AxC1:          ∅ ⊢ AxiomC1 t₁ t₂
| AxC2:          ∅ ⊢ AxiomC2 t₁ t₂ t₃
| AxP1:          ∅ ⊢ AxiomP1 t₁ t₂
| AxP2:          ∅ ⊢ AxiomP2 t₁ t₂ t₃
| AxS1:          ∅ ⊢ AxiomS1 t₁ t₂
| AxS2:          ∅ ⊢ AxiomS2 t₁ t₂ t₃
| AxS3:          ∅ ⊢ AxiomS3 a f b x
-- TBD: FALTA AXS4

end

def bAC (x y f : String) (A : Formula) : Formula := (∀₁₁ x (∃₁₁ y A)) →₁ (∃₁₁ f (∀₁₁ x (b∃₁₁ y ((Term.var f)·(Term.var x)) A)))     -- bAC^ω_*

local infix:27 (priority := high) " ⊢ " => ProvableFrom     -- já não é a mesma notação que em ProvableFrom!

/- A formula is provable if there is a -/
/-
This definition states that a formula A is considered provable
if it can be derived (or proved) from an empty set of assumptions.
In other words, Provable A holds true if A can be proved purely
by the logical rules defined in the ProvableFrom inductive type,
without relying on any specific assumptions.
-/
-- DEF: A formula is said to be provable if it can be derived using ProvableFrom and nothing else
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}

/- We define a simple tactic `apply_ax` to prove something using the `ax` rule. -/
syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_insert | apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

/-
se não teriamos de usar os seguintes lemas about insert:
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
-/


-- Define the reflexivity proof for terms
/-
theorem term_reflexivity {t:Term}: ∅ ⊢ (t =₁ t) :=
  match t with
  | var x => by refine ProvableFrom.contrad ?_
  | Term.lcons l => by simp
  | Term.app t1 t2 => by simp [term_reflexivity t1, term_reflexivity t2]
-/

example (A : Formula) : (insert (bAC x y f B) ∅ ⊢ A) → (Provable A) := by sorry
theorem Soundness (A : Formula) : (insert (bAC x y f B) ∅ ⊢ A) → (∃(t:Term), (Provable (∀₁ a A))) := by sorry    -- TBD: falta subst aqui
theorem Characterization (A : Formula) : (insert (bAC x y f B) ∅ ⊢ A) → (Provable (A ∨₁ A)) := by sorry          -- TBD: falta A^SH aqui
lemma Lem32 (A : Formula) (hA : isBase A) : (insert (bAC x y f B) ∅ ⊢ ((b∀₁₁ x t (∃₁₁ y A)) →₁ (∃₁₁ b (b∀₁₁ x t (b∃₁₁ y (var b) A))))) := by sorry


example : insert A (insert B ∅) ⊢ A ∧₁ B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_insert _ _)))

example : insert A (insert B ∅) ⊢ A ∧₁ B := by
  exact andI (by apply_ax) (by apply_ax)

/-
example : insert A (insert B ∅) ⊢ A ∧₁ B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_insert _ _)))

example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (by apply_ax) (by apply_ax)
-/




/-

/- A formula is provable if there is a -/
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}

-/
