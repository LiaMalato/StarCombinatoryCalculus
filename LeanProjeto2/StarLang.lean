-- -------------------------------------------------------------
--            Star Language (atualizada)
-- -------------------------------------------------------------

-- We import the definitions from the first-order language L:
import LeanProjeto2.FOL
import MathLib.Tactic

namespace StarLang

-- Finite types [def 1.1]
inductive FType : Type
| ground : FType                        -- G
| arrow : FType → FType → FType         -- σ → τ
| star : FType → FType                  -- σ*

open FType

-- Notation for finite types
def G := ground                         -- notation G => ground
notation t "⟶" t1 => arrow t t1
notation t "⋆" => star t

-- ----------------------------
-- TERMS and CONSTANTS (p.9-12)
-- ----------------------------

-- def Sym : Type := String deriving BEq, DecidableEq, Repr

-- DEFINITION 1.2 (p.8-9): Terms of L^{omega}_*
inductive Term --where
| lcons : LTerm → Term                  -- L-constants
| pi                                    -- combinators:     Π
| sigma                                 --                  Σ
| sing                                  -- star constants:  𝔰
| bUnion                                --                  ∪ (binary union)
| iUnion                                --                  ∪ (indexed union)
| var : String → Term                   -- variables
| app : Term → Term → Term              -- application of terms
--deriving Repr                                                                     -- DÁ ERRO

-- NOTATION: Notation for combinators and star constants
notation "Π₁" => Term.pi
notation "Σ₁" => Term.sigma
notation "𝔰₁" => Term.sing
notation "∪₁" => Term.bUnion
notation "ind_⋃₁" => Term.iUnion
notation t₁ "·" t₂ => Term.app t₁ t₂

open Term

-- ------------------------------------------------------
-- TYPECHECKING THE TERMS OF L^{omega}_*
-- We typecheck the components of the formulas of L^ω_*.
-- This guarantees that the formulas have admissible types.
-- ------------------------------------------------------

inductive Term_TypeChecking : Term → FType → Prop
| tcLcons (t : LTerm) : Term_TypeChecking (lcons t) G                                                           -- L-constants have type G
| tcPi {σ τ} : Term_TypeChecking pi (σ ⟶ (τ ⟶ σ))                                                             -- Π_{σ,τ} : σ ⟶ (τ ⟶ σ)
| tcSigma {σ τ ρ}: Term_TypeChecking sigma ((σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ)))                           -- Σ_{σ,τ,ρ} : (σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ))
| tcSing {σ}: Term_TypeChecking sing (σ ⟶ σ⋆)                                                                  -- 𝔰_{σ} : σ⋆
| tcBUnion {σ}: Term_TypeChecking bUnion (σ⋆ ⟶ (σ⋆ ⟶ σ⋆))                                                      -- ∪_{σ} : σ⋆ ⟶ (σ⋆ ⟶ σ⋆)
| tcIUnion {σ τ} : Term_TypeChecking iUnion (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆))                                            -- ∪_{σ} : σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆)
| tcVar {x σ}: Term_TypeChecking (var x) σ                                                                       -- Variables x : σ
| tcApp {t₁ t₂ σ τ}: Term_TypeChecking t₁ (σ ⟶ τ) → Term_TypeChecking t₂ σ → Term_TypeChecking (app t₁ t₂) τ    -- If t₁ : (σ ⟶ τ) and t₂ : σ, then t₁t₂ : τ

open Term_TypeChecking


-- ------------------
-- FORMULAS (p.12-14)
-- ------------------

/-
We define the formulas of L^ω_*:
  a) The atomic formulas (definition 1.6 - p.11)
  b) The base formulas (definition 1.10 - p.14)
  c) The formulas (definition 1.7 - p.13)
-/

inductive Formula
| L_Form : LFormula → Formula
| rel : string → List Term → Formula                                -- R(t₁, ..., tₙ) with R relational symbol of L and t₁,...,tₙ ground terms in L^{omega}_*
| eq : Term → Term → Formula                                        -- t =σ q
| mem : Term → Term → Formula                                       -- t ∈σ q
| not : Formula → Formula                                           -- If A is a formula, then so is (¬A)
| or : Formula → Formula → Formula                                  -- If A and B are formulas, then so is (A∨B)
| unbForall : string → Formula → Formula                            -- If A is a base formula, then so is (∀x A)
| bForall : string → Term → Formula → Formula                       -- If A is a formula, then so is (∀x∈t A)


open Formula

-- NOTATION: Notation for the equality and the membership symbols
notation t₁ "=₁" t₂ => Formula.eq t₁ t₂
notation t₁ "∈₁" t₂ => Formula.mem t₁ t₂

-- NOTATION: Notation for the primitive symbols ¬, ∨, ∀x and ∀x∈t in L^{omega}_*
notation "¬₁" A => not A
notation A "∨₁" B => or A B
notation "V₁" => unbForall
notation "bV₁" => bForall
-- notation "b∀₁" x t A => bForall x t A

-- DEFINITION 1.8 (p.14): The bounded existential quantifier ∃x∈t (defined symbol)

-- The unbounded existential quantifier ∃x A
def E₁ (x : string) (A : Formula) : Formula :=
  ¬₁(unbForall x (¬₁ A))

-- The bounded existential quantifier ∃x A
def bE₁ (x : string) (t : Term) (A : Formula) : Formula :=
  ¬₁(bForall x t (¬₁ A))

-- Testing the notation
-- def Notation_test (x : string) (t : Term) (A : Formula) : Formula := bV₁ x t A
-- #check Notation_test

-- --------------------
-- DEFINED SYMBOLS (p.8 and p.14):
-- Usual logical abbreviations for the defined symbols ∧, →, ↔, ∃x and ∃x∈t in L^{omega}_*
-- --------------------

-- Conjunction:  A ∧ B := ¬(¬A∨¬B)
@[simp]
def F_and (A B : Formula) : Formula :=
  ¬₁ ((¬₁ A) ∨₁ (¬₁ B))

notation A "∧₁" B => F_and A B

-- Implication:  A → B := ¬ A ∨ B
@[simp]
def F_implies (A B : Formula) : Formula :=
  (¬₁ A) ∨₁ B

notation A "→₁" B => F_implies A B

-- Equivalence:  A ↔ B := (A → B) ∧ (B → A)
@[simp]
def F_iff (A B : Formula) : Formula :=
  ¬₁ ((¬₁((¬₁A) ∨₁ B)) ∨₁ (¬₁((¬₁B) ∨₁ A)))
  -- (A →₁ B) ∧₁ (B →₁ A)
  -- (¬₁ A ∨₁ B) ∧₁ (¬₁ B ∨₁ A)

notation A "↔₁" B => F_iff A B

-- ------------------------------------------------------
-- CHECKING FORMULAS:
-- ------------------------------------------------------

-- Checks whether a given formula is atomic:
inductive isAtomic : Formula → Prop
| at_rel : isAtomic (rel x l_term)
| at_eq : isAtomic (eq t₁ t₂)
| at_mem : isAtomic (mem t₁ t₂)

-- Checks whether a given formula is base:
inductive isBase : Formula → Prop
| b_atom : isAtomic A → isBase A                                                -- Atomic formulas are base formulas
| b_not (h: isBase A) : isBase (not A)                                          -- If A is base, then so is ¬₁A
| b_or (h1: isBase A) (h2 : isBase B) : isBase (or A B)                         -- If A and B are base, then so is A∨₁B
| b_bForall (x : string) (t : Term) (h : isBase A) : isBase (bForall x t A)     -- If A is base, then so is ∀x∈t A

open isBase

-- Example: Let A be an atomic formula (assumption h), then it is base.
example (A : Formula) (h : isAtomic A)  : (isBase A) := by
  exact b_atom h

example (A B : Formula) (hA_at : isAtomic A) (hB_b : isBase B) : (isBase (A∨₁B)) := by
  have h := b_atom hA_at
  exact b_or h hB_b

-- ------------------------------------------------------
-- LEMMAS: Defined symbols of base formulas are also base
-- ------------------------------------------------------

-- Lemma Conj_base states that if A and B are base formulas, then so is their conjunction A ∧ B
lemma Conj_base (A B : Formula) (hA : isBase A) (hB : isBase B) : (isBase (A∧₁B)) := by
  unfold F_and
  have h_nA := b_not hA
  have h_nB := b_not hB
  have h_or_nAnB := b_or h_nA h_nB
  exact b_not h_or_nAnB

-- Lemma Imp_base states that if A and B are base formulas, then so is their implication A → B
lemma Imp_base (A B : Formula) (hA : isBase A) (hB : isBase B) : (isBase (A→₁B)) := by
  unfold F_implies
  have h_nA := b_not hA
  exact b_or h_nA hB

-- Lemma Iff_base states that if A and B are base formulas, then so is their equivalence A ↔ B
lemma Iff_base (A B : Formula) (hA : isBase A) (hB : isBase B) : (isBase (A↔₁B)) := by
  unfold F_iff
  have h_nA := b_not hA
  have h_nB := b_not hB
  have h_or_nAB := b_or h_nA hB
  have h_or_nBA := b_or h_nB hA
  have h_n_or_nAB := b_not h_or_nAB
  have h_n_or_nBA := b_not h_or_nBA
  have H := b_or h_n_or_nAB h_n_or_nBA
  exact b_not H

-- Lemma unbForall_base states that if A is a base formula, then so is ∀x∈t A
lemma unbForall_base (A : Formula) (x : string) (t : Term) (hA : isBase A) : (isBase (bE₁ x t A)) := by
  unfold bE₁
  have h_nA := b_not hA
  have h_unbForall_nA := b_bForall x t h_nA
  exact b_not h_unbForall_nA

-- ------------------------------------------------------
-- TYPECHECKING
-- We typecheck the components of the formulas of L^ω_*.
-- This guarantees that the formulas have admissible types.
-- ------------------------------------------------------

inductive Formula_TypeChecking : Formula → Prop
| tcRel {R l_terms} :                                               -- R é relational symbol DE L (falta); l_terms é uma lista de termos
    (∀ t, t ∈ l_terms → Term_TypeChecking t G) →
    Formula_TypeChecking (Formula.rel R l_terms)
| tcEq {σ t₁ t₂} :
    Term_TypeChecking t₁ σ →
    Term_TypeChecking t₂ σ →
    Formula_TypeChecking (Formula.eq t₁ t₂)
| tcMem {σ t₁ t₂} :
    Term_TypeChecking t₁ σ →
    Term_TypeChecking t₂ (σ⋆) →
    Formula_TypeChecking (Formula.mem t₁ t₂)
| tcNot {A} :
    Formula_TypeChecking A → Formula_TypeChecking (Formula.not A)
| tcOr {A B} :
    Formula_TypeChecking A →
    Formula_TypeChecking B →
    Formula_TypeChecking (Formula.or A B)
| tcbForall {x σ t A} :
    Term_TypeChecking (Term.var x) σ →
    Term_TypeChecking t (σ⋆) →
    Formula_TypeChecking A →
    Formula_TypeChecking (Formula.bForall x t A)
| tcunbForall {x σ A} :
    Term_TypeChecking (Term.var x) σ →
    Formula_TypeChecking A →
    Formula_TypeChecking (Formula.unbForall x A)


-- --------------------------------------
-- AXIOMS
-- --------------------------------------

--def normal_form (A B : Formula) (x: string) : Formula → Formula
--| or A B => A
--| bForall x A => A
--| t => t

-- Drei strecher ass gleich, wees net wei dat heescht
inductive Equivalent : Formula → Formula → Prop
| id : Equivalent A A
| comm : Equivalent A B → Equivalent B A
--| nf_left : Equivalent A B → Equivalent (normal_form A) B
--| nf_right : Equivalent A B → Equivalent A (normal_form B)

inductive isTrue : Formula → Prop
| lem : isTrue (A ∨₁ (¬₁A))
--| substitution : FALTA
| expansion:
      isTrue A →
      ---------------
      isTrue (A ∨₁ B)
| contraction :
      isTrue (A ∨₁ A) →
      ---------------
      isTrue A
| associativity :
      isTrue (A ∨₁ (B ∨₁ C)) →
      ---------------
      isTrue ((A ∨₁ B) ∨₁ C)
| cut :
      isTrue (A ∨₁ B) →
      isTrue ((¬₁A)∨₁C) →
      ---------------
      isTrue (B ∨₁ C)
--| forall_introduction : FALTA
| equivalence :
      (Equivalent A B) →
      isTrue A →
      isTrue B
| AxE₁ (x : String) :
    isTrue ((var x) =₁ (var x))
--| AxE₂ (x y : String) : isTrue ((((var x) =₁ (var y))∧₁ A) →₁ A)        FALTA: falta A(x) e A(y)
| AxU (x : String) (t : Term) (A : Formula) :
    isTrue ((bV₁ x t A) ↔₁ (V₁ x (((var x) ∈₁ t) →₁ A)))
| AxC₁ (t₁ t₂ : Term) :
    isTrue (((Π₁·t₁)·t₂) =₁ t₁)
| AxC₂ (t₁ t₂ t₃ : Term) :
    isTrue ((((Σ₁·t₁)·t₂)·t₃) =₁ ((t₁·t₃)·(t₂·t₃)))
| AxP₁ (t₁ t₂ : Term) :
    isTrue (((ind_⋃₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁))
| AxP₂ (t₁ t₂ t₃ : Term) :
    isTrue (((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) =₁ ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)))
| AxS₁ (t₁ t₂ : Term) :
    isTrue ((t₁ ∈₁ (𝔰₁·t₂)) ↔₁ (t₁ =₁ t₂))
| AxS₂ (t₁ t₂ t₃ : Term) : isTrue ((t₁ ∈₁ ((∪₁·t₂)·t₃) ) ↔₁ ((t₁ ∈₁ t₂) ∨₁ (t₁ ∈₁ t₃)))
| AxS₃ (a f b : Term) : isTrue ((b ∈₁ ((ind_⋃₁·a)·f)) ↔₁ (bE₁ x a (b ∈₁ (f·x))))

-- FALTA: falta o bAC^ω_*

-- TESTE: o lemma eq_symmetry está a dar erro, mas o teste com #check mostra que a sintaxe está good
def f : Term := var "f"
def g : Term := var "g"

#check (f =₁ g) →₁ (g =₁ f)

--lemma eq_symmetry : (f =₁ g) →₁ (g =₁ f) := sorry

--theorem tastino (x y : String) : Formula

--lemma eq_symmetry (x y : String) : (((var x) =₁ (var y)) →₁ ((var y) =₁ (var x))) := sorry

--lemma eq_transitivity (x y z : String) : ((((var x) =₁ (var y)) ∧₁ ((var y) =₁ (var z))) →₁ ((var x) =₁ (var z))) := sorry

-- --------------------------------------
-- COVERSIONS
-- --------------------------------------

-- Checks whether a term converts to another one
inductive ConvertsTo : Term → Term → Prop
| c1_pi {t₁ t₂}: ConvertsTo ((Π₁·t₁)·t₂) t₁
| c2_sigma {t₁ t₂ t₃}: ConvertsTo (((Σ₁·t₁)·t₂)·t₃) ((t₁·t₃)·(t₂·t₃))
| c3_indU {t₁ t₂} : ConvertsTo ((ind_⋃₁·(𝔰₁·t₁))·t₂) (t₂·t₁)
| c4_indU_binU {t₁ t₂ t₃}: ConvertsTo ((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃))

def conv : Term → Term
| ((Π₁·t₁)·t₂) => t₁
| ((Σ₁·t₁)·t₂)·t₃ => (t₁·t₃)·(t₂·t₃)
| (ind_⋃₁·(𝔰₁·t₁))·t₂ => t₂·t₁
| (ind_⋃₁·((∪₁·t₁)·t₂))·t₃ => (∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)
| t => t

def examplinho (q t : Term) := ((Π₁·q)·t)
--#eval examplinho                                FALTA: falta o REPR que está a dar erro

--notation t₁ "▹" t₂ => conv t₁ t₂

-- FALTA: conversions preserve types

-- EXAMPLE 1.10 (p.28)


end StarLang
