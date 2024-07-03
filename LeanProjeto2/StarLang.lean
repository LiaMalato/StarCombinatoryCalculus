import LeanProjeto2.FOL

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

-- --------------------------
-- TERMS E CONSTANTS (p.9-12)
-- --------------------------

-- DEFINITION 1.2 (p.8-9): Terms of L^{omega}_*
inductive Term
| lcons : LTerm → Term                  -- L-constants
| pi                                    -- combinators:     Π
| sigma                                 --                  Σ
| sing                                  -- star constants:  𝔰
| bUnion                                --                  ∪ (binary union)
| iUnion                                --                  ∪ (indexed union)
| var : string → Term                   -- variables
| app : Term → Term → Term              -- application of terms

open Term

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

-- NOTATION: Notation for combinators and star constants
notation "Π₁" => Term.pi
notation "Σ₁" => Term.sigma
notation "𝔰₁" => Term.sing
notation "∪₁" => Term.bUnion
notation "ind_⋃₁" => Term.iUnion
--notation "⁅"t₁ t₂"⁆" => Term.app t₁ t₂


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
--notation t₁ "=_"σ t₂ => AtomicFormula.eq σ t₁ t₂
notation t₁ "∈_"σ t₂ => AtomicFormula.mem σ t₁ t₂

open AtomicFormula

-- DEFINITION 1.10 (p.14): Base formulas of L^{omega}_*
inductive BaseFormula
| batom : AtomicFormula → BaseFormula                                   -- Atomic formulas are base formulas
| bnot : BaseFormula → BaseFormula                                      -- If A is a base formula, then so is (¬A)
| bor : BaseFormula → BaseFormula → BaseFormula                         -- If A and B are base formulas, then so is (A∨B)
| bboundedForall : string → FType → Term → BaseFormula → BaseFormula    -- If A is a base formula, then so is (∀x∈t A)

--#check (A : AtomicFormula) batom A
def SomeFormula (A : AtomicFormula) : BaseFormula := BaseFormula.batom A
#check SomeFormula

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

open BaseFormula
open Formula

-- NOTATION: Notation for the primitive symbols ¬, ∨, ∀x and ∀x∈t in L^{omega}_*
notation "¬₁" A => Fnot A
notation A "∨₁" B => For A B
notation "b∀₁" x σ t A => FboundedForall x σ t A
notation "∀₁" x σ A => FunboundedForall x σ A


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
--def Fexists (x : var) (A : Formula) : Formula :=
--  ¬₁ (∀₁ x (¬₁ A))

notation A "↔₁" B => Fiff A B
-- notation "∃₀" x A => exists_L x A

-- ∃x A := ¬ (∀x (¬ A))                                -- NOT WORKING
--def lexists (x : LVar) (A : LFormula) : LFormula :=
--  ¬₁ (∀₁ x (¬₁ A))

-- --------------------------------------

-- DEFINITION 1.8 (p.14): The bounded existential quantifier ∃x∈t (defined symbol)



-- --------------------
-- Acrescentar algo que checks whether a formula is base or not
--  + acrescentar que simbolos definidos também deixam as base formulas closed
-- --------------------

def isBase : Formula → Bool
| Fbase _ => true
| _ => false

#check isBase

-- Function to check if a formula is a base formula
--@[simp]
def isBaseFormula : Formula → Bool
| Fbase _ => true
| ¬₁ (Fbase _) => true
| (Fbase _) ∨₁ (Fbase _) => true
| FboundedForall _ _ _ (Formula.Fbase _) => true
| _ => false

-- Ex1.4(1). tx : τ where t : σ → τ and x : σ
example (σ τ : FType) (t : Term) (x : string) (h1: TypeChecking t (σ ⟶ τ)) (h2 : TypeChecking (var x) σ) : TypeChecking (app t (var x)) τ :=
  by
   exact TypeChecking.tcApp h1 h2

lemma teste1 (A : BaseFormula) (hA : isBaseFormula (Fbase A)) (hB : isBaseFormula (Fbase B)) : isBaseFormula ((Fbase A) ∨₁ (Fbase B)) :=
  by
    simp [isBaseFormula]

#check teste1



-- Lemma: ¬₁ ((¬₁ A) ∨₁ (¬₁ B)) is a base formula
--AQUIlemma neg_disjunction_is_base_formula (A B : BaseFormula) (h: bnot (bor (bnot A) (bnot B))) : BaseFormula := sorry
--begin
  -- Apply the bor and bnot constructors to form the desired formula
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
    -- Simplify using the definition of Fand
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

-- Symmetry of equality   WRONG -> precisamos de TypeChecking?
--theorem symmetry_of_eq (σ : FType) (x y : string): AtomicFormula.eq σ (var x) (var y) → AtomicFormula.eq σ (var y) (var x) := sorry
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


def AxC₁ (σ : FType) (p q : Term) : AtomicFormula       -- FALTA TYPECHECKING
  := eq σ (app (app Π₁ p) q) q

def AxC₂ (τ : FType) (p q t : Term) : AtomicFormula     -- FALTA TYPECHECKING
  := eq τ (app (app (app Σ₁ p) q) t) (app (app p t) (app q t))

--def AxP₁ (τ : FType) (x y : Term) : AtomicFormula
--  :=


end StarLang
