-- -------------------------------------------------------------
--            STAR LANGUAGE - THE SYNTAX
-- -------------------------------------------------------------

-- We import the definitions from the first-order language L:
import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import MathLib.Tactic
import Init.Data.List.Basic
import Init.Data.List.Lemmas

open FOLang
open LFormula

-- ----------------------------
-- TERMS and CONSTANTS (p.9-12)
-- ----------------------------

-- DEFINITION 1.2 (p.8-9): Terms of L^{omega}_*
inductive Term --where
| lcons : LTerm → Term                  -- L-constants
| pi --{σ τ: FType} : Term                                    -- combinators:     Π
| sigma --{σ τ ρ: FType} : Term                               --                  Σ
| sing                                  -- star constants:  𝔰
| bUnion                                --                  ∪ (binary union)
| iUnion                                --                  ∪ (indexed union)
| var : String → Term                   -- variables
| app : Term → Term → Term              -- application of terms
deriving Repr, DecidableEq

open Term

-- EXAMPLE: some terms to use in future examples
def var_x := var "x"
def var_y := var "y"
def var_z := var "z"
def lcons_a (a:LTerm) := lcons a
def lcons_k (k:LTerm) := lcons k
def lcons_var_y := lcons (Lvar_y)

-- --------------------------------
-- TERMS OF TUPLES (new)
-- --------------------------------

def TermTuple := List Term
deriving BEq, Repr

-- This function takes a list of Term and makes a term tuple out of it
def makeTuple (ts : List Term) : TermTuple := ts

-- We define a function in order to access any element in the tuple
def getElement (n : Nat) (t : TermTuple) : Option Term :=           -- Option para ter some/none para o caso do tuple ter 2 elementos e pedirmos o terceiro
  List.get? t n

-- -------
-- EXAMPLE: a tuple of terms + access to its elements (new)
-- -------

def exTermTuple : TermTuple := makeTuple ([var_x, var_y])  -- a tuple of terms (a list with the terms x and a)

#eval getElement 0 exTermTuple          -- Output: var_x (the first element of exTermTuple)
#eval getElement 1 exTermTuple          -- Output: var_y (the second element of exTermTuple)
#eval getElement 2 exTermTuple          -- Output: none (there is no third element in exTermTuple)


-- --------------------------------
-- WELL-FORMED TERMS
-- --------------------------------

-- Helper function to check if an LTerm is well-formed        TODO: Repetido no FOLanguage as LTerm_is_wellformed
inductive LTerm_is_wellformed_inStar : List String → LTerm → Prop
-- a variable is well-formed if that variable is in the given list of variables
| wf_var {xs x} : x ∈ xs → LTerm_is_wellformed_inStar xs (LTerm.Lvar x)
| wf_const {xs c} : LTerm_is_wellformed_inStar xs (LTerm.Lconst c)
| wf_func {xs f ts} : (∀ t ∈ ts, LTerm_is_wellformed_inStar xs t) → LTerm_is_wellformed_inStar xs (LTerm.Lfunc f ts)

-- Define Term_is_wellformed for Term
inductive Term_is_wellformed : List String → Term → Prop
| wf_lcons {xs} {t : LTerm} : LTerm_is_wellformed_inStar xs t → Term_is_wellformed xs (lcons t)           -- TODO not now: não sei porque com LTerm.LTerm_is_wellformed não funciona tbm
| wf_pi {xs} : Term_is_wellformed xs pi
| wf_sigma {xs} : Term_is_wellformed xs sigma
| wf_sing {xs} : Term_is_wellformed xs sing
| wf_bUnion {xs} : Term_is_wellformed xs bUnion
| wf_iUnion {xs} : Term_is_wellformed xs iUnion
| wf_var {xs x} : x ∈ xs → Term_is_wellformed xs (var x)
| wf_app {xs t1 t2} : Term_is_wellformed xs t1 → Term_is_wellformed xs t2 → Term_is_wellformed xs (app t1 t2)

-- Definition: well-formed tuple of terms (new)
inductive TermTuple_is_wellformed : List String → List Term → Prop
| wf_tuple : (∀ t ∈ ts, Term_is_wellformed xs t) → (TermTuple_is_wellformed xs ts)

-- --------
-- Example:
-- --------

-- Next example: mostrar que var_x is well-formed under the list of variables ["x", "y"]
-- (List.mem_cons_self "x" ["y"]) states que "x" pertence à lista [ "x","y" ]
example : Term_is_wellformed ["x", "y"] var_x := Term_is_wellformed.wf_var (List.mem_cons_self "x" ["y"])

-- --------------------------------
-- SUBTERM
-- --------------------------------

namespace Term

-- DEFINITION: subterm of a term
inductive isSubterm : Term → Term → Prop
| refl (t : Term) : isSubterm t t                                                             -- Terms are always subterms of themselves
| app_left {t₁ t₂ t' : Term} : isSubterm t' t₁ → isSubterm t' (Term.app t₁ t₂)                  -- Subterms of applications (LHS)
| app_right {t₁ t₂ t' : Term} : isSubterm t' t₂ → isSubterm t' (Term.app t₁ t₂)                 -- Subterms of applications (RHS)

open isSubterm

-- Example: example of a subterm
example : isSubterm (var "x") (app (var "x") (var "y")) :=
  by
    have H := isSubterm.refl (var "x")
    exact app_left H

/-
-- Examples of subterms
example : isSubterm (var "x") ((var "x")·(var "y")) :=
  app_left refl

example : isSubterm (Term.var "y") (Term.app (Term.var "x") (Term.var "y")) :=
  app_right refl
-/

-- DEFINITION: subterm of a tuple of terms
inductive isSubtermTuple : TermTuple → TermTuple → Prop
| empty_subtuple : isSubtermTuple [] []                                      -- Empty tuple is a subtuple of itself
| rec_subtuple {t₁ t₂ : Term} {ts₁ ts₂ : TermTuple} :                       -- Recursive definition for non-empty tuples
    isSubterm t₁ t₂ →
    isSubtermTuple ts₁ ts₂ →
    isSubtermTuple (t₁ :: ts₁) (t₂ :: ts₂)

-- -------------------------------------
-- FREE VARIABLES PARA TERMOS EM L^ω_*
-- -------------------------------------

-- DEFINITION: all the (free) variables of terms in StarLang
def freevars : Term → Finset String                           -- TODO: mudar este nome para term_vars?
| lcons t => t.Lfreevars                                      --       since para terms: vars and free_vars it's the same
| pi
| sigma
| sing
| bUnion
| iUnion => {}
| var x => {x}
| app t₁ t₂ => t₁.freevars ∪ t₂.freevars

-- DEFINITION: (free) variables in tuples of terms
--             (freevars returns the set of (free) variables)
def freevarsTuple (tuple : TermTuple) : Finset String :=
  (tuple.map freevars).foldl (fun acc fv => acc ∪ fv) ∅

-- ---------------------------------------
-- CLOSED TERMS
-- ---------------------------------------

def isClosedTerm (t : Term) : Prop := freevars t = {}
def isClosedTupleTerm (t : TermTuple) : Prop := freevarsTuple t = {}

-- ------------------------------------------------------------
-- NOTATION FOR THE COMBINATORS AND THE STAR CONSTANTS IN L^ω_* (and the application of terms)
-- ------------------------------------------------------------

-- NOTATION: Notation for combinators and star constants
notation "Π₁" => Term.pi
notation "Σ₁" => Term.sigma
notation "𝔰₁" => Term.sing
notation "∪₁" => Term.bUnion
notation "ind_⋃₁" => Term.iUnion
notation t₁ "·" t₂ => Term.app t₁ t₂

-- ------------------------------------------------------
-- TYPECHECKING THE TERMS OF L^{omega}_*
-- ------------------------------------------------------

-- DEFINITION: Term_TypeChecking a term
-- We typecheck the components of the formulas of L^ω_*.
-- This guarantees that the formulas have admissible types.
inductive Term_TypeChecking : Term → FType → Prop
| tcLcons (t : LTerm) : Term_TypeChecking (lcons t) G                                                           -- L-constants have type G
| tcPi {σ τ} : Term_TypeChecking pi (σ ⟶ (τ ⟶ σ))                                                             -- Π_{σ,τ} : σ ⟶ (τ ⟶ σ)
| tcSigma {σ τ ρ}: Term_TypeChecking sigma ((σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ)))                           -- Σ_{σ,τ,ρ} : (σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ))
| tcSing {σ}: Term_TypeChecking sing (σ ⟶ σ⋆)                                                                  -- 𝔰_{σ} : σ⋆
| tcBUnion {σ}: Term_TypeChecking bUnion (σ⋆ ⟶ (σ⋆ ⟶ σ⋆))                                                      -- ∪_{σ} : σ⋆ ⟶ (σ⋆ ⟶ σ⋆)
| tcIUnion {σ τ} : Term_TypeChecking iUnion (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆))                                            -- ∪_{σ} : σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆)
| tcVar {x σ}: Term_TypeChecking (var x) σ                                                                       -- Variables x : σ
| tcApp {t₁ t₂ σ τ}: Term_TypeChecking t₁ (σ ⟶ τ) → Term_TypeChecking t₂ σ → Term_TypeChecking (app t₁ t₂) τ    -- If t₁ : (σ ⟶ τ) and t₂ : σ, then t₁t₂ : τ

-- DEFINITION: Term_TypeChecking a tuple of terms
-- Para que um tuple of terms seja typechecked checkamos se o primeiro termo tem o primeiro tipo da lista de tipos
-- e depois o resto dos termos no tuple também têm os tipos correspondentes no resto da lista de tipos.
inductive TermTuple_TypeChecking : TermTuple → List FType → Prop
--| tcEmptyTuple : TermTuple_TypeChecking [] []
| tcRecTuple {t : Term} {σ : FType} {ts : TermTuple} {σs : List FType} :
    Term_TypeChecking t σ →
    TermTuple_TypeChecking ts σs →
    TermTuple_TypeChecking (t :: ts) (σ :: σs)

open Term_TypeChecking


-- -------------------------------------
-- TERM SUBSTITUTION IN L^ω_*
-- -------------------------------------

-- Definition: term substitution, we replace x by replacement in some term t (lcons, var, app, rest)
def term_substitution (x : String) (replacement : Term) : Term → Term
| lcons t => match replacement with
              | lcons r => lcons (LTerm.Lsubstitution x r t)                        -- Since replacement has to be an LTerm, we have to add this pattern matching
              | _ => lcons t
| var y => if x = y
          then replacement
          else (var y)
| app t₁ t₂ => app (term_substitution x replacement t₁) (term_substitution x replacement t₂)  -- In an application, we do the substitution in each term
| t => t                                                                              -- The combinators Π, Σ and the star constants 𝔰, ∪, ind_⋃ are constants and hence are not affected by substitution

-- Definição de substituição de tuple terms: Substituimos _ por _ em _ (new)
def term_substitutionTuple (x : String) (replacement : Term) : TermTuple → TermTuple
| [] => []
| (t :: ts) => (term_substitution x replacement t) :: term_substitutionTuple x replacement ts

-- EXAMPLES: substituting in terms
#eval term_substitution "x" Π₁ (var_x)                                        -- Replacing x by Π₁ in x gives Π₁
#eval term_substitution "x" Π₁ (var_y)                                        -- Replacing x by Π₁ in y gives y
#eval term_substitution "x" ∪₁ (((var_x)·(var_y))·(var_z))                    -- Replacing x by ∪₁ in (x·y)·z gives (∪₁·y)·z
#eval term_substitution "x" (lcons (LTerm.Lvar "b")) (lcons (LTerm.Lvar "a")) -- Replacing x by (Lvariable b) in (Lvariable a) gives (Lvariable a) -> nothing happens

-- EXAMPLE: substituting in tuple of terms
-- We substitute "x" by an lconstant a in the tuple [x, (y·z)]
#eval term_substitutionTuple "x" (lcons (Lconst_a)) [var_x, (Π₁·var_y)]       -- Output: [a, (Π₁·z)]


-- ---------------------------------------------------------------------------------------

-- ------------------
-- FORMULAS (p.12-14)
-- ------------------

/-
We define the formulas of L^ω_*:
  a) The atomic formulas (definition 1.6 - p.11)
  b) The base formulas (definition 1.10 - p.14)
  c) The formulas (definition 1.7 - p.13)
-/

inductive Formula : Type
| L_Form : LFormula → Formula
| rel : String → List Term → Formula                              -- R(t₁, ..., tₙ) with R relational symbol of L and t₁,...,tₙ ground terms in L^{omega}_*
| eq : Term → Term → Formula                                      -- t =σ q
| mem : Term → Term → Formula                                     -- t ∈σ q
| not : Formula → Formula                                         -- If A is a formula, then so is (¬A)
| or : Formula → Formula → Formula                                -- If A and B are formulas, then so is (A∨B)
| unbForall : String → Formula → Formula                        -- If A is a base formula, then so is (∀x A)
| bForall : String → Term → Formula → Formula                     -- If A is a formula, then so is (∀x∈t A)
deriving Repr
--| bForall {x: String} {t:Term} {h: x ∉ t.freevars} : String → Term → Formula → Formula          -- TO DO: passar para well-formed temos de acrescentar isto

-- Convertemos a lista de variáveis numa nested sequence de quantificadores `forall`
def unbForallTuple (vars : List String) (A : Formula) : Formula :=
  vars.foldr (fun v acc =>
    Formula.unbForall v acc
  ) A

-- TODO: check this: do we need TermTuple?
def bForallTuple (vars : List String) (t : Term) (A : Formula) : Formula :=
  vars.foldr (fun v acc =>
    Formula.bForall v t acc
  ) A

open Formula

-- Helper function: well-formed FOL formulas in L^ω_*
inductive LFormula_is_wellformed_inStar : List String → LFormula → Prop
| wf_atomic {xs P ts} :
    (∀ t ∈ ts, LTerm_is_wellformed_inStar xs t) →
    LFormula_is_wellformed_inStar xs (LFormula.atomic_L P ts)                -- If t₁,...,tₙ are well-formed terms, then so is P(t₁,...,tₙ)
| wf_not {xs A} :
    LFormula_is_wellformed_inStar xs A →
    LFormula_is_wellformed_inStar xs (LFormula.not_L A)                      -- If A is a well-formed formula, then so is ¬A.
| wf_or {xs A B} :
    LFormula_is_wellformed_inStar xs A →
    LFormula_is_wellformed_inStar xs B →
    LFormula_is_wellformed_inStar xs (LFormula.or_L A B)                     -- If A and B are well-formed formulas, then so is A∨B.
| wf_forall {xs x A} :
    LFormula_is_wellformed_inStar (x :: xs) A →
    LFormula_is_wellformed_inStar xs (LFormula.forall_L x A)                 -- If A is a well-formed formula (for our list xs and the bound variable x), then so is ∀x A.

-- Definition: well-formed formulas in L^ω_*
inductive Formula_is_wellformed : List String → Formula → Prop
| wf_L_Form {xs} {A : LFormula} : LFormula_is_wellformed_inStar xs A → Formula_is_wellformed xs (L_Form A)
| wf_rel {xs P ts} :
    (∀ t ∈ ts, Term_is_wellformed xs t) → Formula_is_wellformed xs (rel P ts)                                       -- If t₁,...,tₙ are well-formed terms, then so is P(t₁,...,tₙ)
| wf_eq {xs t₁ t₂} :
    Term_is_wellformed xs t₁ → Term_is_wellformed xs t₂ → Formula_is_wellformed xs (eq t₁ t₂)
| wf_mem {xs t₁ t₂} :
    Term_is_wellformed xs t₁ → Term_is_wellformed xs t₂ → Formula_is_wellformed xs (mem t₁ t₂)
| wf_not {xs A} :
    Formula_is_wellformed xs A → Formula_is_wellformed xs (not A)                                                   -- If A is a well-formed formula, then so is ¬A.
| wf_or {xs A B} :
    Formula_is_wellformed xs A → Formula_is_wellformed xs B → Formula_is_wellformed xs (or A B)                     -- If A and B are well-formed formulas, then so is A∨B.
| wf_unbForall {xs x A} :
    Formula_is_wellformed (x :: xs) A → Formula_is_wellformed xs (unbForall x A)                                    -- If A is a well-formed formula (for our list xs and the bound variable x), then so is ∀x A.
| wf_bForall {xs x t A} :
    Formula_is_wellformed (x :: xs) A → Formula_is_wellformed xs (bForall x t A)

-- -------------------------------------
-- FREE VARIABLES PARA FORMULAS EM L^ω_*
-- -------------------------------------

-- DEFINITION: the free variables of a formula in StarLang
def Formula.freevars : Formula → Finset String
| .L_Form (A : LFormula) => LFormula.Lfreevars_formula A
| .rel _ ts => Finset.fold (fun x y => x ∪ y) {} Term.freevars ts.toFinset
| .eq t₁ t₂
| .mem t₁ t₂ => t₁.freevars ∪ t₂.freevars
| .or A B => A.freevars ∪ B.freevars
| .not A => A.freevars
| .unbForall x A
| .bForall x t A => A.freevars \ ([x].toFinset)


-- DEFINITION: all the variables of a formula in StarLang
def Formula.allvars : Formula → Finset String
| .L_Form A => LFormula.Lallvars_formula A                                    -- The variables of a Formula are the ones of the formula when seen as an LFormula
| .rel _ ts => Finset.fold (fun x y => x ∪ y) {} Term.freevars ts.toFinset    -- All the variables from the list of terms used in the predicate
| .eq t₁ t₂
| .mem t₁ t₂ => t₁.freevars ∪ t₂.freevars                                     -- For both terms, we collect the variables from both and consider the union of those sets
| .or A B => A.allvars ∪ B.allvars                                            -- Take the variables from both subformulas and consider the union of those sets
| .not A => A.allvars                                                         -- The variables of ¬A are the ones of A
| .unbForall x A => A.allvars ∪ {x}                                           -- The variables of ∀x A are the ones of A together with the bound variable
| .bForall x t A => t.freevars ∪ A.allvars ∪ {x}                              -- The variables of ∀x∈t A are the ones of A together with the bound variable and the variables in t

-- Example after notation

/-
With these definitions, we can create assumptions such as:
    x is a free variable of formula A       -> In Lean: x ∈ A.freevars
    x is not a free variable of formula A   -> In Lean: x ∉ A.freevars

    x is a variable of formula A            -> In Lean: x ∈ A.allvars
    x is not a variable of formula A        -> In Lean: x ∉ A.allvars
-/

-- -------------------------
-- NOTATION: PRIMITE SYMBOLS
-- -------------------------

-- NOTATION: Notation for the equality and the membership symbols
notation t₁ "=₁" t₂ => Formula.eq t₁ t₂
notation t₁ "∈₁" t₂ => Formula.mem t₁ t₂

-- NOTATION: Notation for the primitive symbols ¬, ∨, ∀x and ∀x∈t in L^{omega}_*
notation "¬₁" A => not A
notation A "∨₁" B => or A B
notation "∀₁₁" => unbForall
notation "b∀₁₁" => bForall
notation "∀₁" => unbForallTuple
notation "b∀₁" => bForallTuple

-- DEFINITION 1.8 (p.14): The bounded existential quantifier ∃x∈t (defined symbol)

-- The unbounded existential quantifier (for one variable): ∃x A := ¬ (∀x (¬ A))
@[simp]
def unbExists (x : String) (A : Formula) : Formula :=
  ¬₁(unbForall x (¬₁ A))

-- The bounded existential quantifier (for one variable) ∃x∈t A := ¬ (∀x∈t (¬ A))
@[simp]
def bExists (x : String) (t : Term) (A : Formula) : Formula :=
  ¬₁(bForall x t (¬₁ A))

-- The unbounded existential quantifier (for a tuple of variables):  ∃x A := ¬ (∀x (¬ A))
@[simp]
def unbExistsTuple (x : List String) (A : Formula) : Formula :=
  ¬₁ (∀₁ x (¬₁A))

-- The bounded existential quantifier (for a tuple of variables):  ∃x∈t A := ¬ (∀x∈t (¬ A))
@[simp]
def bExistsTuple (x : List String) (t : Term) (A : Formula) : Formula :=
  ¬₁ (b∀₁ x t (¬₁A))

notation "∃₁₁" => unbExists
notation "b∃₁₁" => bExists
notation "∃₁" => unbExistsTuple
notation "b∃₁" => bExistsTuple

-- -------------------------
-- NOTATION: DEFINED SYMBOLS (p.8 and p.14):
-- Usual logical abbreviations for the defined symbols ∧, →, ↔, ∃x and ∃x∈t in L^{omega}_*
-- -------------------------

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

-- EXAMPLE OF FREE VARIABLES AND VARIABLES OF A FORMULA
-- Formula R(x,y) ∨ (∀z∈t Q(z)) - Free variables and check whether sentence
def ex_freevars_formula := (rel "R" [var "x", var "y"]) ∨₁ (b∀₁₁ "z" (var "t") (rel "Q" [var "z"]))
#eval Formula.freevars ex_freevars_formula            -- The set of free variables is the set {x,y}, that is {"x", "y"}
#eval Formula.allvars ex_freevars_formula             -- TODO: aqui aparece t como variável, é preciso mudar var "t" aqui e nos exemplos em baixo


-- ----------------------------
-- SENTENCES (CLOSED FORMULAS)
-- ----------------------------

def isClosed (A : Formula) : Prop := Formula.freevars A = {}
def isClosed_check (A : Formula) : Bool := (Formula.freevars A) = {}       -- Prints true or false dependendo se temos var livres ou não

-- EXAMPLE 1: Formula R(x,y) ∨ (∀z∈t Q(z)) - Free variables and check whether sentence
def ex1_freevars_formula := (rel "R" [var "x", var "y"]) ∨₁ (b∀₁₁ "z" (var "t") (rel "Q" [var "z"]))
#eval Formula.freevars ex1_freevars_formula                         -- The set of free variables is the set {x,y}, that is {"x", "y"}
#eval isClosed_check ex1_freevars_formula                           -- Since ex1_freevars_formula has x and y as free variables, the output is false

-- EXAMPLE 2: Formula R(x,y) - Free variables and check whether sentence
def ex2_freevars_formula := (rel "R" [var "x", var "y"])
#eval Formula.freevars ex2_freevars_formula                         -- The set of free variables is the set {x,y}, that is {"x", "y"}
#eval isClosed_check ex2_freevars_formula                           -- Since ex2_freevars_formula has x and y as free variables, the output is false

-- EXAMPLE 3: Formula ∀z∈t Q(z) - Free variables and check whether sentence
def ex3_freevars_formula := (b∀₁₁ "z" (var "t") (rel "Q" [var "z"]))
#eval Formula.freevars ex3_freevars_formula                         -- The set of free variables is the empty set ∅
#eval isClosed_check ex3_freevars_formula                           -- Since ex3_freevars_formula has no free variables, the output is true


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
| b_bForall (x : String) (t : Term) (h : isBase A) : isBase (bForall x t A)     -- If A is base, then so is ∀x∈t A

open isBase

-- Example: Let A be an atomic formula (assumption h), then it is base.
example (A : Formula) (h : isAtomic A)  : (isBase A) := by
  exact b_atom h

example (A B : Formula) (hA_at : isAtomic A) (hB_b : isBase B) : (isBase (A∨₁B)) := by
  have h := b_atom hA_at
  exact b_or h hB_b




-- --------------------------------------------------------------------------
-- LEMMAS: Defined symbols of base formulas are also base (Remark 1.11, p.14)
-- --------------------------------------------------------------------------

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

-- Lemma unbForall_base states that if A is a base formula, then so is ∃x∈t A
lemma bExists_base {A : Formula} (x : String) (t : Term) (hA : isBase A) : (isBase (b∃₁₁ x t A)) := by
  unfold bExists
  have h_nA := b_not hA
  have h_unbForall_nA := b_bForall x t h_nA
  exact b_not h_unbForall_nA

-- ------------------
-- EXAMPLE 1.6 (p.14)
-- ------------------

-- Example 1.6.1 (p.14): If B is a base formula, then so is ∀x∈t B(x)
example (B : Formula) (hB_b : isBase B) (x : String) (t : Term): (isBase (b∀₁₁ x t (¬₁ B))) := by
  have H := b_not hB_b
  exact b_bForall x t H

-- Example 1.6.2 (p.14): If A and B are base formulas, then so is ∀x∈t ∃y∈q (A∨B)
example (A B : Formula) (hA_b : isBase A) (hB_b : isBase B) (x y : String) (t q : Term): (isBase (b∀₁₁ x t (b∃₁₁ y q (A ∨₁ B)))) := by
  have H_or_AB := b_or hA_b hB_b
  have H_bExists := bExists_base y q H_or_AB
  exact b_bForall x t H_bExists

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

-- -------------------------------------
-- FORMULA SUBSTITUTION IN L^ω_*
-- -------------------------------------

def substitution_formula (x : String) (replacement : Term) : Formula → Formula
| (L_Form A) => match replacement with
              | .lcons r => L_Form (LFormula.Lsubstitution_formula x r A)
              | _ => (L_Form A)
| (rel P terms) => rel P (terms.map (term_substitution x replacement))
| (t₁ =₁ t₂) => (term_substitution x replacement t₁) =₁ (term_substitution x replacement t₂)
| (t₁ ∈₁ t₂) => (term_substitution x replacement t₁) ∈₁ (term_substitution x replacement t₂)
| (Formula.not A) => ¬₁ (substitution_formula x replacement A)                                                       -- recursivamente em A
| (Formula.or A B) => (substitution_formula x replacement A) ∨₁ (substitution_formula x replacement B)               -- recursivamente em A e B
| (∀₁₁ y A) => if x = y then ∀₁₁ y A
              else ∀₁₁ y (substitution_formula x replacement A)
| (b∀₁₁ y t A) => if x = y then b∀₁₁ y t A
              else (b∀₁₁ y t (substitution_formula x replacement A))


-- EXAMPLES: formula substitution           -- TODO: falta o repr para podermos ter estes examplos com #eval

-- Example 1:
#eval substitution_formula "x" Π₁ (rel "R" [var_x, var_y])        -- Output: R(Π₁,y)

-- Example 2:
def ex2_subst : Formula :=
    (¬₁( (var "x")∈₁(var "y") )) ∨₁ ((var "z")=₁(var "w"))
#eval substitution_formula "z" ∪₁ ex2_subst                       -- Output: (¬₁(x ∈₁ y)) ∨₁ (∪₁ =₁ w)

-- Example 3:
def ex3_subst : Formula :=
  bForall "y" (var "a") ((var "x")=₁(var "y"))
#eval substitution_formula "x" ind_⋃₁ ex3_subst                   -- Output: ∀ y ∈ a (ind_⋃₁ =₁ y)


/- Próximas tarefas:
      1. Truly check a cena do ∀x∈t, what is tuple, what is not and how to interpretar
      2. Fazer fórmulas com A(t) em que t é fórmula and how to interpretar
          + o que tem de ser alterado nas defs das fórmulas
      3. Fazer simultaneous substitution (terms and formulas)
      4. Prenexificação aqui
-/
