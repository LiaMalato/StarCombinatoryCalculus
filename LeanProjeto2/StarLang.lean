import LeanProjeto2.FOL

namespace StarLang

-- Finite types [def 1.1]
inductive FType : Type
| ground : FType                 -- G
| arrow : FType → FType → FType  -- σ → τ   arrow : FType → (FType → (FType → FType))
| star : FType → FType           -- σ*

open FType

-- notation G => ground
def G := ground
notation t "⟶" t1 => arrow t t1
notation t "⋆" => star t

-- EXAMPLE 1.2
def ex1Type1 : FType := G⋆                                           -- 1.2.1 G*
def ex1Type2 : FType := G ⟶ G                                        -- G → G
def ex1Type31 : FType := G ⟶ (G ⟶ G)                                -- G → (G → G)
def ex1Type32 : FType := (G ⟶ G) ⟶ G                                -- (G → G) → G
def ex1Type4 : FType := (G ⟶ G) ⟶ (G ⟶ (G ⟶ G))                   -- (G → G) → (G → (G → G))
def ex1Type51 (σ τ : FType) : FType := σ ⟶ ((σ⋆ ⟶ τ) ⟶ τ)          -- σ → ((σ* → τ) → τ)
def ex1Type52 (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆                     -- 1.2.5 (σ* → τ)*
example (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆

#check ex1Type32 -- ???????????
#check ex1Type51

-- --------------------
-- TERMOS E CONSTANTES
-- --------------------

-- DEFINITION 1.2
inductive Term -- Falta acrescentar as L-constants
| pi                  -- ??? COMO LIDAR COM A "ARIDADE", para termos Pi, Pi x, Pi xy -> term application
| sigma
| sing
| bUnion
| iUnion
| var : string → Term
| app : Term → Term → Term
--| disjunction : Term → Term → Term
--| negation : Term → Term
--| universal : string → FType → Term → Term
--| equality : FType → Term → Term → Term
--| membership : FType → Term → Term → Term
--| boundedUniversal : string → FType → Term → Term → Term

-- Os quantificadores não são termos
--| universal : string → Term → Term
--| universalBounded : string → Term → Term → Term

--#check Term.universalBounded "x" Term.pi Term.pi

open Term

inductive TypeChecking : Term → FType → Prop     -- Falta L-constants
| tcPi {σ τ} : TypeChecking pi (σ ⟶ (τ ⟶ σ))
| tcSigma {σ τ ρ}: TypeChecking sigma ((σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ)))
| tcSing {σ}: TypeChecking sing (σ ⟶ σ⋆)
| tcBUnion {σ}: TypeChecking bUnion (σ⋆ ⟶ (σ⋆ ⟶ σ⋆))
| tcIUnion {σ τ} : TypeChecking iUnion (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆))
| tcVar {x σ}: TypeChecking (var x) σ
| tcApp {t₁ t₂ σ τ}: TypeChecking t₁ (σ ⟶ τ) → TypeChecking t₂ σ → TypeChecking (app t₁ t₂) τ
--| tcDisjunction {t₁ t₂ σ} : TypeChecking t₁ σ → TypeChecking t₂ σ → TypeChecking (disjunction t₁ t₂) σ
--| tcNegation {t σ} : TypeChecking t σ → TypeChecking (negation t) σ
--| tcUniversal {x σ t τ} : (∀ x, TypeChecking (var x) σ → TypeChecking t τ) → TypeChecking (universal x σ t) (σ ⟶ τ)
-- NEEDED? | tcEquality {σ t₁ t₂} : TypeChecking t₁ σ → TypeChecking t₂ σ → TypeChecking (equality σ t₁ t₂) (σ ⟶ σ ⟶ σ)
-- NEEDED? | tcMembership {σ t₁ t₂} : TypeChecking t₁ σ → TypeChecking t₂ (σ⋆) → TypeChecking (membership σ t₁ t₂) (σ ⟶ σ⋆ ⟶ σ)
--| tcBoundedUniversal {x σ t₁ t₂ τ} : TypeChecking t₁ (σ⋆) → (∀ x, TypeChecking (var x) σ → TypeChecking t₂ τ) → TypeChecking (boundedUniversal x σ t₁ t₂) (σ ⟶ τ)
-- Os quantificadores não são termos
--| tcUniversal {x : string} {σ τ : FType} : TypeChecking x σ → TypeChecking (universal x σ) (σ ⟶ τ) → TypeChecking (universal x σ) τ
--| tcUniv {x t σ}: TypeChecking x σ → TypeChecking t σ⋆

-- --------------------
-- FORMULAS
-- --------------------

inductive AtomicFormula
| rel : string → List Term → AtomicFormula  -- R(t₁, ..., tₙ)  --> TYPE CHECK?
| eq : FType → Term → Term → AtomicFormula  -- t =σ q     --> TYPE CHECK? OR USE PREVIOUS?
| mem : FType → Term → Term → AtomicFormula -- t ∈σ q

notation t₁ "=_"σ t₂ => AtomicFormula.eq σ t₁ t₂
notation t₁ "∈_"σ t₂ => AtomicFormula.mem σ t₁ t₂

open AtomicFormula

inductive BaseFormula
| batom : AtomicFormula → BaseFormula
| bnot : BaseFormula → BaseFormula
| bor : BaseFormula → BaseFormula → BaseFormula
| bboundedForall : string → FType → Term → BaseFormula → BaseFormula  -- ∀x^σ ∈ t. A

open BaseFormula

inductive Formula
| Fatom : AtomicFormula → Formula
| Fnot : Formula → Formula
| For : Formula → Formula → Formula
| FboundedForall : string → FType → Term → Formula → Formula  -- ∀x^σ ∈ t. A
| FunboundedForall : string → FType → Formula → Formula       -- ∀x^σ. A

open Formula

notation "¬₁" A => Fnot A
notation A "∨₁" B => For A B
notation "∀₁" x σ t A => FboundedForall x σ t A
notation "∀₁" x σ A => FunboundedForall x σ A

-- --------------------
-- ABREVIATURAS
-- --------------------

-- falta definir as abreviaturas





-- --------------------
-- Acrescentar algo que checks whether a formula is base or not
-- --------------------



-- --------------------
-- AXIOMS
-- --------------------

-- SHOENFIELD'S CALCULUS (Axiom 1.1)

-- -----------------------------------------------------------------------------------
-- -------------------------- AXIOM SCHEMA -------------------------------------------
-- -----------------------------------------------------------------------------------

-- Axiom schema:

-- --------------------------- Excluded middle ---------------------------------------
-- Excluded middle

-- axiom ExcMid (A : Formula) : (¬₁ A) ∨₁ A
-- axiom ExcMid (A : Formula) : For (Fnot A) A

-- Excluded middle DEFINITION
def excluded_middle_axiom (A : Formula) : Formula :=
  (¬₁ A) ∨₁ A
--  For (Fnot A) A

-- Excluded middle AXIOM + AXIOM INSTANCE
axiom excluded_mid_axiom (A : Formula) : Formula
axiom excluded_mid_instance (A : Formula) : excluded_middle_axiom A = (¬₁ A) ∨₁ A

-- --------------------------- Substitution (TBDone)---------------------------------
-- Substituion

-- -----------------------------------------------------------------------------------
-- --------------------------- RULES -------------------------------------------------
-- -----------------------------------------------------------------------------------

-- Rules:

-- --------------------------- Expansion ---------------------------------------------
-- Expansion

def expansion_r (A B : Formula) : Formula :=
  B ∨₁ A

axiom expansion_rule (A B : Formula) : Formula
axiom expansion_instance (A B : Formula) : expansion_rule A B = B ∨₁ A

-- --------------------------- Contraction ------------------------------------------
-- Contraction

def contraction_r (A : Formula) : Formula :=
  A ∨₁ A

axiom contraction_rule (A : Formula) : Formula
axiom contraction_instance (A : Formula) : contraction_rule A = A ∨₁ A

-- --------------------------- Associativity ----------------------------------------
-- Associativity

-- def associativity_r (A B C : Formula) (h : A ∨₁ (B ∨₁ C)) : Formula :=
--   (A ∨₁ B) ∨₁ C

-- axiom associativity_rule (A B C : Formula) : Formula
-- axiom associativity_instance (A B C : Formula) : associativity_rule A B C = A ∨₁ (B ∨₁ C) → (A ∨₁ B) ∨₁ C

-- --------------------------- Cut --------------------------------------------------
-- Cut

-- --------------------------- ∀-introduction ---------------------------------------
-- ∀-introduction






-- EQUALITY AXIOMS (Axiom 1.2)



-- AXIOM FOR THE BOUNDED UNIVERSAL QUANTIFIER (Axiom 1.3)



-- COMBINATOR AXIOMS (Axiom 1.4)



-- PRIMARY AXIOMS FOR THE STAR CONSTANTS (Axiom 1.5)




-- SECONDARY AXIOMS FOR THE STAR CONSTANTS (Axiom 1.6)



-- BOUNDED AXIOM OF CHOICE (Axiom 1.7)
