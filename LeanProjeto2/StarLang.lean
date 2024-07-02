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
| pi
| sigma
| sing
| bUnion
| iUnion
| var : string → Term
| app : Term → Term → Term

open Term

inductive TypeChecking : Term → FType → Prop     -- Falta L-constants
| tcPi {σ τ} : TypeChecking pi (σ ⟶ (τ ⟶ σ))
| tcSigma {σ τ ρ}: TypeChecking sigma ((σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ)))
| tcSing {σ}: TypeChecking sing (σ ⟶ σ⋆)
| tcBUnion {σ}: TypeChecking bUnion (σ⋆ ⟶ (σ⋆ ⟶ σ⋆))
| tcIUnion {σ τ} : TypeChecking iUnion (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆))
| tcVar {x σ}: TypeChecking (var x) σ
| tcApp {t₁ t₂ σ τ}: TypeChecking t₁ (σ ⟶ τ) → TypeChecking t₂ σ → TypeChecking (app t₁ t₂) τ

open TypeChecking

notation "Π₁" => Term.pi
notation "Σ₁" => Term.sigma
notation "𝔰₁" => Term.sing
notation "∪₁" => Term.bUnion
notation "ind_⋃₁" => Term.iUnion
--notation "⁅"t₁ t₂"⁆" => Term.app t₁ t₂

--example (t : Term) (x: var) :=
--  TypeChecking.tcApp t x σ τ


-- -------------------------------------
-- EXAMPLE 1.3: cenas com tuples (tipos)
-- -------------------------------------

-- -------------------------
-- EXAMPLE 1.4: [p.10/11]
--  p: (σ → τ) → τ → ρ
--  q : σ ⟶ τ ⟶ ρ
--  r : ρ ⟶ σ
--  s : ρ ⟶ σ
--  t : σ → τ
--  w : σ ⟶ τ⋆
--  x : σ
--  y : τ
-- -------------------------

-- Ex1.4(1). t₁t₂ : τ where t₁ : σ → τ and t₂ : σ
example (σ τ : FType) (t₁ t₂ : Term) (h1: TypeChecking t₁ (σ ⟶ τ)) (h2 : TypeChecking t₂ σ) : TypeChecking (app t₁ t₂) τ := by
  exact (TypeChecking.tcApp h1 h2)

-- Ex1.4(1). tx : τ where t : σ → τ and x : σ
example (σ τ : FType) (t : Term) (x : string) (h1: TypeChecking t (σ ⟶ τ)) (h2 : TypeChecking (var x) σ) : TypeChecking (app t (var x)) τ := by
  exact (TypeChecking.tcApp h1 h2)

-- Ex1.4(2). (pt)(tx) : ρ where p: (σ → τ) → τ → ρ, t : σ → τ and x : σ
example (σ τ ρ : FType) (p t : Term) (x: string) (h1 : TypeChecking p ((σ⟶τ)⟶τ⟶ρ)) (h2: TypeChecking t (σ ⟶ τ)) (h3 : TypeChecking (var x) σ) : TypeChecking (app (app p t) (app t (var x))) ρ := by
  have H1 := TypeChecking.tcApp h1 h2
  have H2 := TypeChecking.tcApp h2 h3
  exact (TypeChecking.tcApp H1 H2)

-- Ex1.4(3) - Π₁_{σ,τ} x : τ ⟶ σ where Π₁ : σ ⟶ τ ⟶ σ and x : σ
example (σ τ : FType) (t : Term) (x : string)
    (h1 : TypeChecking (var x) σ)
    (h2 : TypeChecking Π₁ (σ ⟶ τ ⟶ σ)) : TypeChecking (app Π₁ (var x)) (τ ⟶ σ) := sorry
-- have H

-- Ex1.4(4) - (Σ₁_{σ,τ,ρ} q)t : ρ ⟶ τ where Σ₁ : (σ ⟶ τ ⟶ ρ) ⟶ (σ ⟶ τ) ⟶ σ ⟶ ρ and t : σ ⟶ τ and x : σ
example (σ τ ρ : FType) (q t : Term)
    (h1 : TypeChecking t (σ ⟶ τ))
    (h2: TypeChecking q (σ ⟶ τ ⟶ ρ)) : TypeChecking (app (app Σ₁ q) t) (ρ ⟶ τ) := sorry

-- Ex1.4(5) -
example (σ τ : FType) (t : Term) (x: string)
    (h1 : TypeChecking t (σ ⟶ τ))
    (h2 : TypeChecking (var x) σ)
    (h3 : TypeChecking Σ₁ ((σ ⟶ τ ⟶ σ) ⟶ (σ ⟶ τ) ⟶ σ ⟶ σ))
    (h4 : TypeChecking Π₁ (σ ⟶ τ ⟶ σ)): TypeChecking (app (app Σ₁ q) t) σ := sorry

-- Ex1.4(6) -
example (σ τ : FType) (w : Term) (x: string)
    (h1 : TypeChecking w (σ ⟶ τ⋆))
    (h2 : TypeChecking (var x) σ)
    (h3 : TypeChecking 𝔰 (σ⋆ ⟶ σ⋆))
    (h4 : TypeChecking ind_⋃₁ (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆)))
    (h5 : TypeChecking ∪₁ (σ⋆ ⟶ (σ⋆ ⟶ σ⋆))) : TypeChecking (app ∪₁ (app (app ind_⋃₁ (app 𝔰 (var x))) w)) (τ⋆ ⟶ τ⋆) := sorry
--  have H1 := TypeChecking (app 𝔰 x) σ⋆
--  have H2 := TypeChecking (app ind_∪₁ (app 𝔰 x)) ((σ ⟶ τ⋆) ⟶ τ⋆)
--  have H3 := TypeChecking (app (app ind_∪₁ (app 𝔰 x)) w) τ⋆
--  have H4 := TypeChecking (app ∪₁ (app (app ind_∪₁ (app 𝔰 x)) w)) (τ⋆ ⟶ τ⋆)

-- ----------------------------------------------
-- EXAMPLE 1.5: cenas com tuples (termos e tipos)
-- ----------------------------------------------


-- --------------------
-- FORMULAS
-- --------------------

inductive AtomicFormula
| rel : string → List Term → AtomicFormula  -- R(t₁, ..., tₙ)
| eq : FType → Term → Term → AtomicFormula  -- t =σ q
| mem : FType → Term → Term → AtomicFormula -- t ∈σ q

-- Type checking for Atomic formulas
inductive AtomicTypeChecking : AtomicFormula → Prop
| tcRel {R l_terms} :                             -- R é relational symbol DE L (falta); l_terms é uma lista de termos
    (∀ t, t ∈ l_terms → TypeChecking t G) →
    AtomicTypeChecking (AtomicFormula.rel R l_terms)
| tcEq {σ t₁ t₂} :
    TypeChecking t₁ σ →
    TypeChecking t₂ σ →
    AtomicTypeChecking (AtomicFormula.eq σ t₁ t₂)
| tcMem {σ t₁ t₂} :
    TypeChecking t₁ σ →
    TypeChecking t₂ (σ⋆) →
    AtomicTypeChecking (AtomicFormula.mem σ t₁ t₂)

notation t₁ "=_"σ t₂ => AtomicFormula.eq σ t₁ t₂
notation t₁ "∈_"σ t₂ => AtomicFormula.mem σ t₁ t₂


open AtomicFormula

inductive BaseFormula
| batom : AtomicFormula → BaseFormula
| bnot : BaseFormula → BaseFormula
| bor : BaseFormula → BaseFormula → BaseFormula
| bboundedForall : string → FType → Term → BaseFormula → BaseFormula  -- ∀x^σ ∈ t. A

inductive Formula
| Fatom : AtomicFormula → Formula
| Fbase : BaseFormula → Formula
| Fnot : Formula → Formula
| For : Formula → Formula → Formula
| FboundedForall : string → FType → Term → Formula → Formula  -- ∀x^σ ∈ t. A
| FunboundedForall : string → FType → Formula → Formula       -- ∀x^σ. A

-- Type checking for Base formulas
inductive BaseFormulaTypeChecking : BaseFormula → Prop
| tcBatom {A} :
    AtomicTypeChecking A →
    BaseFormulaTypeChecking (BaseFormula.batom A)
| tcBnot {A} :
    BaseFormulaTypeChecking A →
    BaseFormulaTypeChecking (BaseFormula.bnot A)
| tcBor {A B} :
    BaseFormulaTypeChecking A →
    BaseFormulaTypeChecking B →
    BaseFormulaTypeChecking (BaseFormula.bor A B)
| tcBboundedForall {x σ t A} :
    TypeChecking (Term.var x) σ →
    TypeChecking t (σ⋆) →
    BaseFormulaTypeChecking A →
    BaseFormulaTypeChecking (BaseFormula.bboundedForall x σ t A)

-- Type checking for Formulas
inductive FormulaTypeChecking : Formula → Prop
| tcFatom {A} :
    AtomicTypeChecking A →
    FormulaTypeChecking (Formula.Fatom A)
| tcFnot {A} :
    FormulaTypeChecking A →
    FormulaTypeChecking (Formula.Fnot A)
| tcFor {A B} :
    FormulaTypeChecking A →
    FormulaTypeChecking B →
    FormulaTypeChecking (Formula.For A B)
| tcFboundedForall {x σ t A} :
    TypeChecking (Term.var x) σ →
    TypeChecking t (σ⋆) →
    FormulaTypeChecking A →
    FormulaTypeChecking (Formula.FboundedForall x σ t A)
| tcFunboundedForall {x σ A} :
    TypeChecking (Term.var x) σ →
    FormulaTypeChecking A →
    FormulaTypeChecking (Formula.FunboundedForall x σ A)

open BaseFormula
open Formula

notation "¬₁" A => Fnot A
notation A "∨₁" B => For A B
notation "∀₁" x σ t A => FboundedForall x σ t A
notation "∀₁" x σ A => FunboundedForall x σ A


-- --------------------
-- ABREVIATURAS
-- --------------------

-- Conjunction:  A ∧ B := ¬(¬A∨¬B)
def Fand (A B : Formula) : Formula :=
  ¬₁ ((¬₁ A) ∨₁ (¬₁ B))

-- Implication:  A → B := ¬ A ∨ B
def Fimplies (A B : Formula) : Formula :=
  (¬₁ A) ∨₁ B

notation A "∧₁" B => Fand A B
notation A "→₁" B => Fimplies A B

-- Equivalence:  A ↔ B := (A → B) ∧ (B → A)
def Fiff (A B : Formula) : Formula :=
  (A →₁ B) ∧₁ (B →₁ A)

-- Existential quantification:  ∃x A := ¬ (∀x (¬ A))
-- def Fexists (x : var) (A : Formula) : Formula :=
--  not_L (forall_L x (not_L A))

notation A "↔₁" B => Fiff A B
-- notation "∃₀" x A => exists_L x A

-- ∃x A := ¬ (∀x (¬ A))                                -- NOT WORKING
--def lexists (x : LVar) (φ : LFormula) : LFormula :=
--  ¬₀ (∀₀ x (¬₀ φ))




-- --------------------
-- Acrescentar algo que checks whether a formula is base or not
-- --------------------

-- ---------------------------------
-- EXAMPLE 1.6: Base formulas or not
-- ---------------------------------



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




-- -----------------------------------------------------------------------------------
-- --------------------------- OTHER AXIOMS -------------------------------------------------
-- -----------------------------------------------------------------------------------


-- EQUALITY AXIOMS (Axiom 1.2)

--axiom equality_reflexivity (σ : FType) (x : var) : Formula :=
--  ∀₀ x (Term.var x =_σ Term.var x)


-- PROPOSITION 1.1: Symmetry and transitivity of equality (higher types)

-- Symmetry of equality   WRONG
-- theorem symmetry_of_eq (x y : σ) : x = y → y = x :=
-- λ h, h.symm

-- Transitivity of equality   WRONG
-- theorem transitivity_of_eq (x y z : σ) : x = y → y = z → x = z :=
-- λ hxy hyz, hxy.trans hyz




-- AXIOM FOR THE BOUNDED UNIVERSAL QUANTIFIER (Axiom 1.3)



-- COMBINATOR AXIOMS (Axiom 1.4)



-- PRIMARY AXIOMS FOR THE STAR CONSTANTS (Axiom 1.5)




-- SECONDARY AXIOMS FOR THE STAR CONSTANTS (Axiom 1.6)



-- BOUNDED AXIOM OF CHOICE (Axiom 1.7)

-- Pattermatching com "lambda por casos"  FAZER PARA OS OUTROS TERMOS
--@[simp]
--def subst (x : string) (p : Term) : Term → Term
--| (var y) => if x=y then p else var y           -- var substitui logo
--| (app e1 e2) => app (subst x p e1) (subst x p e2)
--| x => x                  -- outra coisa qualquer


end StarLang
