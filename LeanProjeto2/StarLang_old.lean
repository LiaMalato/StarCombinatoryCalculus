-- -------------------------------------------------------------
--            Star Language (desatualizada)
-- -------------------------------------------------------------

import LeanProjeto2.FOL

namespace StarLang_old

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

-- --------------------------
-- TERMS E CONSTANTS (p.9-12)
-- --------------------------

def Sym : Type := String deriving BEq, DecidableEq, Repr

-- DEFINITION 1.2 (p.8-9): Terms of L^{omega}_*
inductive Term --where
| lcons : LTerm → Term                  -- L-constants
| pi                                    -- combinators:     Π
| sigma                                 --                  Σ
| sing                                  -- star constants:  𝔰
| bUnion                                --                  ∪ (binary union)
| iUnion                                --                  ∪ (indexed union)
| var : string → Term                   -- variables
| app : Term → Term → Term              -- application of terms
--deriving BEq, DecidableEq, Repr

--namespace Term
-- Notation for Terms
--infixl:70 " □ " => app
--prefix:90 "` " => var

-- (x:string) (var x)

-- NOTATION: Notation for combinators and star constants
notation "Π₁" => Term.pi
notation "Σ₁" => Term.sigma
notation "𝔰₁" => Term.sing
notation "∪₁" => Term.bUnion
notation "ind_⋃₁" => Term.iUnion
notation t₁ "·" t₂ => Term.app t₁ t₂
--notation "⁅"t₁ t₂"⁆" => Term.app t₁ t₂

open Term

/-
-- Substitution function for Terms
def subst : Term → Sym → Term → Term
| (var x), y, v => if x = y then v else var x
| pi, _, _ => pi
| sigma, _, _ => sigma
| sing, _, _ => sing
| bUnion, _, _ => bUnion
| iUnion, _, _ => iUnion
| (app l m), y, v => app (subst l y v) (subst m y v)
-/


-- Typing the terms of L^{omega}_*   (term type checking)
inductive TypeChecking : Term → FType → Prop
| tcLcons (t : LTerm) : TypeChecking (lcons t) G                                                  -- L-constants have type G
| tcPi {σ τ} : TypeChecking pi (σ ⟶ (τ ⟶ σ))                                                    -- Π_{σ,τ} : σ ⟶ (τ ⟶ σ)
| tcSigma {σ τ ρ}: TypeChecking sigma ((σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ)))                  -- Σ_{σ,τ,ρ} : (σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ))
| tcSing {σ}: TypeChecking sing (σ ⟶ σ⋆)                                                         -- 𝔰_{σ} : σ⋆
| tcBUnion {σ}: TypeChecking bUnion (σ⋆ ⟶ (σ⋆ ⟶ σ⋆))                                            -- ∪_{σ} : σ⋆ ⟶ (σ⋆ ⟶ σ⋆)
| tcIUnion {σ τ} : TypeChecking iUnion (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆))                                   -- ∪_{σ} : σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆)
| tcVar {x σ}: TypeChecking (var x) σ                                                             -- Variables x : σ
| tcApp {t₁ t₂ σ τ}: TypeChecking t₁ (σ ⟶ τ) → TypeChecking t₂ σ → TypeChecking (app t₁ t₂) τ    -- If t₁ : (σ ⟶ τ) and t₂ : σ, then t₁t₂ : τ

open TypeChecking


-- ------------------
-- FORMULAS (p.12-14)
-- ------------------

-- DEFINITION 1.6 (p.11): Atomic formulas of L^{omega}_*
inductive AtomicFormula
| lForm : LFormula → AtomicFormula                                  -- Remark 1.9: The atomic formulas of L^{omega}_* include the atomic formulas of L
| rel : string → List Term → AtomicFormula                          -- R(t₁, ..., tₙ) with R relational symbol of L and t₁,...,tₙ ground terms in L^{omega}_*
| eq : FType → Term → Term → AtomicFormula                          -- t =σ q
| mem : FType → Term → Term → AtomicFormula                         -- t ∈σ q

-- Typing the components of the atomic formulas of L^{omega}_* (atomic formulas type checking)
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

-- NOTATION: Notation for the equality and the membership symbols
--notation t₁ "=_" t₂ => AtomicFormula.eq t₁ t₂
--notation t₁ "∈_"σ t₂ => AtomicFormula.mem σ t₁ t₂

open AtomicFormula

-- DEFINITION 1.10 (p.14): Base formulas of L^{omega}_*
inductive BaseFormula
| batom : AtomicFormula → BaseFormula                                   -- Atomic formulas are base formulas
| bnot : BaseFormula → BaseFormula                                      -- If A is a base formula, then so is (¬A)
| bor : BaseFormula → BaseFormula → BaseFormula                         -- If A and B are base formulas, then so is (A∨B)
| bboundedForall : string → FType → Term → BaseFormula → BaseFormula    -- If A is a base formula, then so is (∀x∈t A)

--#check (A : AtomicFormula) batom A
def SomeFormula (A : AtomicFormula) : BaseFormula := BaseFormula.batom A        -- TESTE
#check SomeFormula                                                              -- TESTE

-- DEFINITION 1.7 (p.13): Formulas of L^{omega}_*
inductive Formula
| Fbase : BaseFormula → Formula                                         -- Base formulas are formulas
| Fnot : Formula → Formula                                              -- If A is a formula, then so is (¬A)
| For : Formula → Formula → Formula                                     -- If A and B are formulas, then so is (A∨B)
| FboundedForall : string → FType → Term → Formula → Formula            -- If A is a formula, then so is (∀x∈t A)
| FunboundedForall : string → FType → Formula → Formula                 -- If A is a base formula, then so is (∀x A)

-- Type checking for base formulas
inductive BaseFormulaTypeChecking : BaseFormula → Prop
| tcBatom {A} :
    AtomicTypeChecking A → BaseFormulaTypeChecking (BaseFormula.batom A)
| tcBnot {A} :
    BaseFormulaTypeChecking A → BaseFormulaTypeChecking (BaseFormula.bnot A)
| tcBor {A B} :
    BaseFormulaTypeChecking A →
    BaseFormulaTypeChecking B →
    BaseFormulaTypeChecking (BaseFormula.bor A B)
| tcBboundedForall {x σ t A} :
    TypeChecking (Term.var x) σ →
    TypeChecking t (σ⋆) →
    BaseFormulaTypeChecking A →
    BaseFormulaTypeChecking (BaseFormula.bboundedForall x σ t A)

-- Type checking for formulas
inductive FormulaTypeChecking : Formula → Prop
| tcFbase {A} :
    BaseFormulaTypeChecking A → FormulaTypeChecking (Formula.Fbase A)
| tcFnot {A} :
    FormulaTypeChecking A → FormulaTypeChecking (Formula.Fnot A)
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

-- COPIED UNTIL HERE

open BaseFormula
open Formula

def AB (A B : Formula) : Formula := Formula.For A B             -- TESTE
def AB2 (A B : Formula) : Formula := For A B                    -- TESTE
def ABC (A B C : Formula) : Formula := For A (For B C)          -- TESTE

-- NOTATION: Notation for the primitive symbols ¬, ∨, ∀x and ∀x∈t in L^{omega}_*
notation "¬₁" A => Fnot A
notation A "∨₁" B => For A B
notation "b∀₁" x σ t A => FboundedForall x σ t A
notation "V₁" x σ A => FunboundedForall x σ A

def ABC2 (A B C : Formula) : Formula := A ∨₁ (B ∨₁ C)           -- TESTE
def ABC3 (A B C : Formula) : Formula := (A ∨₁ B) ∨₁ C           -- TESTE
#check ABC2                                                     -- TESTE
--def ABCABC2 (A B C : Formula) : Formula → Formula := (ABC2 A B C) → (ABC3 A B C)
--def ABCABC (A B C : Formula) : Formula → Formula := A ∨₁ (B ∨₁ C) → (A ∨₁ B) ∨₁ C

-- --------------------
-- DEFINED SYMBOLS: Usual logical abbreviations for the defined symbols ∧, →, ↔, ∃x and ∃x∈t in L^{omega}_* (p.8 and p.14)
-- --------------------

-- Conjunction:  A ∧ B := ¬(¬A∨¬B)
@[simp]
def Fand (A B : Formula) : Formula :=
  ¬₁ ((¬₁ A) ∨₁ (¬₁ B))
-- have (¬₁ ((¬₁ A) ∨₁ (¬₁ B))) by

-- Implication:  A → B := ¬ A ∨ B
@[simp]
def Fimplies (A B : Formula) : Formula :=
  (¬₁ A) ∨₁ B

notation A "∧₁" B => Fand A B
notation A "→₁" B => Fimplies A B

-- Equivalence:  A ↔ B := (A → B) ∧ (B → A)
@[simp]
def Fiff (A B : Formula) : Formula :=
  (A →₁ B) ∧₁ (B →₁ A)

-- Existential quantification:  ∃x A := ¬ (∀x (¬ A))
--def Fexists (x : string) (σ : FType) (A : Formula) : Formula :=
--  ¬₁(∀₁ "x" σ (¬₁A))

notation A "↔₁" B => Fiff A B
-- notation "∃₀" x A => exists_L x A

-- ∃x A := ¬ (∀x (¬ A))                                 -- TESTE
--def lexists (x : LVar) (A : LFormula) : LFormula :=   -- TESTE
--  ¬₁ (∀₁ x (¬₁ A))                                    -- TESTE

def teste3 (A : Formula) := ¬₁(¬₁ A)                    -- TESTE
#check teste3                                           -- TESTE

-- --------------------------------------
-- Notation for the bounded and unbounded universal quantifier

def V (x : string) (σ : FType) (A : Formula) : Formula := FunboundedForall x σ A
def bV (x : string) (σ : FType) (t : Term) (A : Formula) : Formula := FboundedForall x σ t A

-- --------------------------------------

-- DEFINITION 1.8 (p.14): The bounded existential quantifier ∃x∈t (defined symbol)

-- F_unb_exists
def E (x : string) (σ : FType) (A : Formula) : Formula :=
  ¬₁(FunboundedForall x σ (¬₁ A))

-- F_b_exists
def bE (x : string) (σ : FType) (t : Term) (A : Formula) : Formula :=
  ¬₁(FboundedForall x σ t (¬₁ A))

-- --------------------
-- Acrescentar algo que checks whether a formula is base or not
--  + acrescentar que simbolos definidos também deixam as base formulas closed
-- --------------------

-- CHECK SE É BASE

def isBase : Formula → Bool
| Fbase _ => true
| _ => false

#check isBase

--@[simp]
def isBaseFormula : Formula → Bool
| Fbase _ => true
| ¬₁ (Fbase _) => true
| (Fbase _) ∨₁ (Fbase _) => true
| FboundedForall _ _ _ (Formula.Fbase _) => true
| _ => false

-- Ex1.4(1). tx : τ where t : σ → τ and x : σ                                 -- TESTE
example (σ τ : FType) (t : Term) (x : string)                                 -- TESTE
    (h1: TypeChecking t (σ ⟶ τ))                                             -- TESTE
    (h2 : TypeChecking (var x) σ) : TypeChecking (app t (var x)) τ :=         -- TESTE
  by                                                                          -- TESTE
   exact TypeChecking.tcApp h1 h2                                             -- TESTE

lemma teste1 (A : BaseFormula)                                                -- TESTE
  (hA : isBaseFormula (Fbase A))                                              -- TESTE
  (hB : isBaseFormula (Fbase B)) : isBaseFormula ((Fbase A) ∨₁ (Fbase B)) :=  -- TESTE
  by                                                                          -- TESTE
    simp [isBaseFormula]                                                      -- TESTE

#check teste1                                                                 -- TESTE



-- Lemma: ¬₁ ((¬₁ A) ∨₁ (¬₁ B)) is a base formula
--AQUIlemma neg_disjunction_is_base_formula (A B : BaseFormula) (h: bnot (bor (bnot A) (bnot B))) : BaseFormula := sorry
--begin
--  exact BaseFormula.bnot (BaseFormula.bor (BaseFormula.bnot A) (BaseFormula.bnot B)),
--end

--example (A : BaseFormula) (hA : isBaseFormula (Fbase A)) (hB : isBaseFormula (Fbase B)) : isBaseFormula ((¬₁ (Fbase A)) ∨₁ (Fbase B)) :=
--  by
--    simp [isBaseFormula]
  -- by
  -- exact isBaseFormula

-- lemma (A B : FBase): (A ∧₁ B) : FBase :=
-- Lemma: if A and B are BaseFormula, then A ∧₁ B is a BaseFormula
--lemma and_is_baseformula (A B : BaseFormula) : isBaseFormula ((Fbase A) ∧₁ (Fbase B)) = true := sorry
  ----by
    -- Acho que devia simplificar usando Fand
    -----simp
    -----have h1 := isBaseFormula ((Fbase A) ∨₁ (Fbase B))
  --by unfold Fand (Fbase A) (Fbase B)
  --by unfold Fand ; simp [isBaseFormula]




-- ----------------------------------------
-- EXAMPLE 1.6 (p.14): Base formulas or not
-- ----------------------------------------

-- example (A : Formula) (B : FBase) (σ τ : FTypes)






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

-- axiom associativity {A B C : Formula} : (A ∨₁ (B ∨₁ C)) → (A ∨₁ B) ∨₁ C


--def associativity_r (A B C : Formula) (h : A ∨₁ (B ∨₁ C)) : Formula :=
--   (A ∨₁ B) ∨₁ C

--def associativity_r (A B C : Formula) (h : (For A (For B C))) : Formula :=
--   For (For A B) C

--def associativity_r (A B : Formula) : Formula → Formula :=
--  A → A

--axiom associativity_rule (A B C : Formula) : Formula
--axiom ass_inst (A B C : Formula) : associativity_rule A B C = (A∨₁(B∨₁C) → (A∨₁B)∨₁C)
--axiom associativity_instance (A B C : Formula) : (associativity_rule A B C) = A ∨₁ (B ∨₁ C) → (A ∨₁ B) ∨₁ C

--axiom associativity (A B C : Formula) : ((A ∨₁ B) ∨₁ C) → (A ∨₁ (B ∨₁ C))

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

-- Symmetry of equality   WRONG -> precisamos de TypeChecking?
--theorem symmetry_of_eq (σ : FType) (x y : string): eq σ (var x) (var y) → eq σ (var y) (var x) := sorry
-- by intro a intro b exact tcEq hx hy
-- λ h, h.symm

-- Types in the symmetry of equality   WRONG -> precisamos de TypeChecking?
--theorem symmetry_of_eq (σ : FType) (x y : string)
--    (hx : TypeChecking (var x) σ)
--    (hy : TypeChecking (var y) σ) : (var x) "=_"σ (var y) → (var y) "=_"σ (var x) := sorry
-- by intro a intro b exact tcEq hx hy
-- λ h, h.symm

-- #check AtomicFormula.eq σ (var x) (var y)

-- Types in the symmetry of equality   WRONG -> precisamos de TypeChecking?
--theorem symmetry_of_eq2 (σ : FType) (x y : string)
--    (hx : TypeChecking (var x) σ)
--    (hy : TypeChecking (var y) σ)
--    (hy : TypeChecking (var y) σ): AtomicFormula.eq σ (var x) (var y) → AtomicFormula.eq σ (var y) (var x) := sorry
-- by intro a intro b exact tcEq hx hy
-- λ h, h.symm

-- notation t₁ "=_"σ t₂ => AtomicFormula.eq σ t₁ t₂

-- Transitivity of equality   WRONG -> precisamos de TypeChecking?
-- theorem transitivity_of_eq (σ : FType) (x y z : string) (hx : TypeChecking.tcVar x σ) (hy : TypeChecking.tcVar y σ) (hz : TypeChecking.tcVar z σ) : (var x) "=_"σ (var y) → (var y) "=_"σ (var z) → (var x) "=_"σ (var z) :=
-- λ hxy hyz, hxy.trans hyz


lemma example_lemma (P Q : Prop) (h : P → Q) (p : P) : Q :=
  h p

-- notation t₁ "=_" t₂ σ => AtomicFormula.eq t₁ t₂ σ

--lemma example_lemma2 (t₁ t₂ : Term) (σ : FType) : (AtomicFormula.eq t₁ t₂ σ) → (AtomicFormula.eq t₁ t₂ σ) := sorry

-- inductive AtomicFormula2
-- | atrel : string → List Term → AtomicFormula2  -- R(t₁, ..., tₙ)
-- | ateq : Term → Term → FType → AtomicFormula2  -- t =σ q
-- | atmem : FType → Term → Term → AtomicFormula2 -- t ∈σ q

-- lemma example_lemma2 (t₁ t₂ : Term) (σ : FType) (h: t₁ "=_" t₂ σ) : (t₁ "=_" t₂ σ) := sorry
--  intro h
--  exact h

-- ----------------------------------------------------------------------------------------------------------
-- ----------------------------------------------------------------------------------------------------------

-- -----------------AXIOM FOR THE BOUNDED UNIVERSAL QUANTIFIER (Axiom 1.3) -----------------

def AxU (σ : FType) (x t : Term) (A : Formula) : Formula            -- FALTA A(x)
  := (bV x σ t A) ↔₁ (V x σ ((Fbase (batom (mem σ x t))) →₁ A))

-- ----------------------------- COMBINATOR AXIOMS (Axiom 1.4) -----------------------------

def AxC₁ (σ : FType) (p q : Term) : AtomicFormula       -- FALTA TYPECHECKING -> TBDONE AS LEMMA
  := eq σ ((Π₁·p)·q) q

-- (h: typechecks pri,eirq tqu qnd  )
def AxC₂ (τ : FType) (p q t : Term) : AtomicFormula     -- FALTA TYPECHECKING
  := eq τ (((Σ₁·p)·q)·t) ((p·t)·(q·t))


-- ---------------- PRIMARY AXIOMS FOR THE STAR CONSTANTS (Axiom 1.5) ----------------------

def AxP₁ (τ : FType) (x y : Term) : AtomicFormula
  := eq (τ⋆) ((ind_⋃₁·(𝔰₁·x))·y) (x·y)

def AxP₂_atom (τ : FType) (x y z : Term) : AtomicFormula
  := eq (τ⋆) ((ind_⋃₁·((∪₁·x)·y))·z) ((∪₁·((ind_⋃₁·x)·z))·((ind_⋃₁·y)·z))

def AxP₂_base (τ : FType) (x y z : Term) : BaseFormula
  := batom (eq (τ⋆) ((ind_⋃₁·((∪₁·x)·y))·z) ((∪₁·((ind_⋃₁·x)·z))·((ind_⋃₁·y)·z)))

def AxP₂_formula (τ : FType) (x y z : Term) : Formula
  := Fbase (batom (eq (τ⋆) ((ind_⋃₁·((∪₁·x)·y))·z) ((∪₁·((ind_⋃₁·x)·z))·((ind_⋃₁·y)·z))))

-- -------------- SECONDARY AXIOMS FOR THE STAR CONSTANTS (Axiom 1.6) ----------------------

def AxS₁ (σ : FType) (x y : Term) : Formula
  := Fbase (batom (mem σ x (𝔰₁·y))) ↔₁ Fbase (batom (eq σ x y))

--def AxS₁_ab (σ : FType) (x y : Term) : Formula                  -- ABBREVIATION NOT WORKING
--  := Fbase (batom (x ∈_ σ (𝔰₁·y))) ↔₁ Fbase (batom (x ∈_ σ y))

def AxS₂ (σ : FType) (x a b: Term) : Formula
  := Fbase (batom ( mem σ x ((∪₁·a)·b) )) ↔₁  ( ( Fbase ((batom (mem σ x a))) ∨₁ Fbase ((batom (mem σ x b)) )))

def AxS₃ (σ : FType) (x a b f : Term) : Formula
  := (Fbase (batom (mem σ b ((ind_⋃₁·a)·f)))) ↔₁ (bE x σ a (Fbase (batom ((mem σ b (f·x))))))

-- ---------------------- BOUNDED AXIOM OF CHOICE (Axiom 1.7) -----------------------------

-- This está meh!! f não tem de ser variável...
def bAC  (x y f : string) (σ : FType) (A : Formula) : Formula        -- FALTA: restricted to base formulas | (x y : var) | tirar tipos
  := (V x σ (E y σ A)) →₁ (E f σ (V x σ (bE y σ ((var f)·(var x)) A)))


-- SUBSTITUIÇAO

-- Pattermatching com "lambda por casos"  FAZER PARA OS OUTROS TERMOS
--@[simp]
--def subst (x : string) (p : Term) : Term → Term
--| (var y) => if x=y then p else var y           -- var substitui logo
--| (app e1 e2) => app (subst x p e1) (subst x p e2)
--| x => x                  -- outra coisa qualquer


/-

def subst (x : string) (y : Sym) (v l m : Term) : Term → Sym → Term → Term
| (var x), y, v => if x = y then v else (var x)
| pi, _, _ => pi
| sigma, _, _ => sigma
| sing, _, _ => sing
| bUnion, _, _ => bUnion
| iUnion, _, _ => iUnion
| (app l m), y, v => app (subst l y v) (subst m y v)

-/


-- CONVERSIONS

-- Primeira conversion
def pi_app_transform : Term → Term
| (Π₁·q)·_ => q
| t => t

-- Example usage
--#eval pi_app_transform p

-- Transformation function?
def pi_app_transform2 : Term → Term
| (Π₁·q)·_ => q   -- Transforma (Π₁·q)·_ em q
| t => t             -- Outros casos ficam

-- def pi_app_transform2 : Term → Term → Term
-- | p q => q
-- | t => t

def example_term (q t : Term) : Term := (Π₁·q)·t
#check example_term




end StarLang_old
