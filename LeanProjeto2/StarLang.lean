-- -------------------------------------------------------------
--            Star Language (atualizada)
-- -------------------------------------------------------------

-- We import the definitions from the first-order language L:
import LeanProjeto2.FOL
import MathLib.Tactic

open FOL
open LFormula

namespace StarLang

-- Finite types [def 1.1]
inductive FType : Type
| ground : FType                        -- G
| arrow : FType → FType → FType         -- σ → τ
| star : FType → FType                  -- σ*
deriving Repr, DecidableEq

open FType

-- Notation for finite types
def G := ground                         -- notation G => ground
notation t "⟶" t1 => arrow t t1
notation t "⋆" => star t

def s1ex2_1 : FType := G⋆
def s1ex2_2 : FType := G ⟶ G
def s1ex2_3 : FType := G ⟶ (G ⟶ G)
def s1ex2_3' : FType := (G ⟶ G) ⟶ G
def s1ex2_4 : FType := (G ⟶ G) ⟶ (G ⟶ (G ⟶ G))
def s1ex2_5 (σ τ : FType) : FType := σ ⟶ ((σ⋆ ⟶ τ) ⟶ τ)
def s1ex2_5' (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆
example (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆

-- ----------------------------
-- TERMS and CONSTANTS (p.9-12)
-- ----------------------------

-- def Sym : Type := String deriving BEq, DecidableEq, Repr

-- DEFINITION 1.2 (p.8-9): Terms of L^{omega}_*
inductive Term --where
| lcons : LTerm → Term                  -- L-constants
| pi --{σ τ: FType} : Term                                    -- combinators:     Π
| sigma --{σ τ ρ: FType} : Term                                --                  Σ
| sing                                  -- star constants:  𝔰
| bUnion                                --                  ∪ (binary union)
| iUnion                                --                  ∪ (indexed union)
| var : String → Term                   -- variables
| app : Term → Term → Term              -- application of terms
deriving Repr, DecidableEq

open Term

-- Helper function to check if an LTerm is well-formed
inductive LTerm_is_wellformed_inStar : List String → LTerm → Prop
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

-- Example usage
def ex_term1 := Term.var "x"
def ex_term2 := Term.lcons (LTerm.Lvar "y")
def ex_term3 := Term.app ex_term1 ex_term2

example : Term_is_wellformed ["x", "y"] ex_term1 := Term_is_wellformed.wf_var (List.mem_cons_self "x" ["y"])
--example : Term_is_wellformed ["x", "y"] ex_term2 := Term_is_wellformed.wf_lcons (LTerm_is_wellformed_inStar.wf_var (List.mem_cons_self "y" ["x"]))
--example : Term_is_wellformed ["x", "y"] ex_term3 := Term_is_wellformed.wf_app (Term_is_wellformed.wf_var (List.mem_cons_self "x" ["y"])) (Term_is_wellformed.wf_lcons (LTerm_is_wellformed_inStar.wf_var (List.mem_cons_self "y" ["x"])))

/-
inductive LTerm : Type
| Lvar : String → LTerm
| Lconst : String → LTerm
| Lfunc : String → List LTerm → LTerm
deriving BEq, Repr

-- Definition: well-formed terms
inductive Term_is_wellformed : List String → LTerm → Prop
| bc_var :
    (x ∈ xs) → Term_is_wellformed xs (Lvar x)                                   -- A variable Lvar x is well-formed if x is in the list
| bc_const :
    Term_is_wellformed xs (Lconst c)                                            -- A constant is always well-formed
| bc_func :
    (∀ t ∈ ts, Term_is_wellformed xs t) → Term_is_wellformed xs (Lfunc f ts)    -- If t₁,...,tₙ are well-formed, then so is f(t₁,...,tₙ)

inductive

-/

namespace Term

-- DEFINITION: subterm _ of a term _
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

def isClosedTerm (t : Term) : Prop := freevars t = {}

end Term

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

-- -------------------------------------
-- TERM SUBSTITUTION IN L^ω_*
-- -------------------------------------

-- Definition: term substitution, we replace x by replacement in some term t (lcons, var, app, rest)
def term_substitution (x : String) (replacement : Term) : Term → Term
| .lcons t => match replacement with
              | .lcons r => .lcons (LTerm.Lsubstitution x r t)                        -- Since replacement has to be an LTerm, we have to add this pattern matching
              | _ => .lcons t
| .var y => if x = y
          then replacement
          else (.var y)
| .app t₁ t₂ => .app (term_substitution x replacement t₁) (term_substitution x replacement t₂)  -- In an application, we do the substitution in each term
| t => t                                                                              -- The combinators Π, Σ and the star constants 𝔰, ∪, ind_⋃ are constants and hence are not affected by substitution

-- EXAMPLES: substituting in terms

#eval term_substitution "x" Π₁ (var "x")                                        -- Replacing x by Π₁ in x gives Π₁
#eval term_substitution "x" Π₁ (var "y")                                        -- Replacing x by Π₁ in y gives y
#eval term_substitution "x" ∪₁ (((var "x")·(var "y"))·(var "z"))                -- Replacing x by ∪₁ in (x·y)·z gives (∪₁·y)·z
#eval term_substitution "x" (lcons (LTerm.Lvar "b")) (lcons (LTerm.Lvar "a"))   -- Replacing x by (Lvariable b) in (Lvariable a) gives (Lvariable a) -> nothing happens


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
| unbForall (x:String) : Formula → Formula                        -- If A is a base formula, then so is (∀x A)
| bForall : String → Term → Formula → Formula                     -- If A is a formula, then so is (∀x∈t A)
deriving Repr
--| bForall {x: String} {t:Term} {h: x ∉ t.freevars} : String → Term → Formula → Formula          -- TO DO: passar para well-formed temos de acrescentar isto
-- deriving Repr, DecidableEq           --TODO: falta incluir isto

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

-- --------
-- NOTATION
-- --------

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
@[simp]
def unbExists (x : String) (A : Formula) : Formula :=
  ¬₁(unbForall x (¬₁ A))

-- The bounded existential quantifier ∃x A
@[simp]
def bExists (x : String) (t : Term) (A : Formula) : Formula :=
  ¬₁(bForall x t (¬₁ A))

notation "E₁" => unbExists
notation "bE₁" => bExists

-- Testing the notation
-- def Notation_test (x : String) (t : Term) (A : Formula) : Formula := bV₁ x t A
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

-- EXAMPLE OF FREE VARIABLES AND VARIABLES OF A FORMULA

-- EXAMPLE 1: Formula R(x,y) ∨ (∀z∈t Q(z)) - Free variables and check whether sentence
def ex_freevars_formula := (rel "R" [var "x", var "y"]) ∨₁ (bV₁ "z" (var "t") (rel "Q" [var "z"]))
#eval Formula.freevars ex_freevars_formula                         -- The set of free variables is the set {x,y}, that is {"x", "y"}
#eval Formula.allvars ex_freevars_formula             -- TODO: aqui aparece t como variável, é preciso mudar var "t" aqui e nos exemplos em baixo


-- ----------------------------
-- SENTENCES (CLOSED FORMULAS)
-- ----------------------------

def isClosed (A : Formula) : Prop := Formula.freevars A = {}
def isClosed_check (A : Formula) : Bool := (Formula.freevars A) = {}       -- Prints true or false dependendo se temos var livres ou não

-- EXAMPLE 1: Formula R(x,y) ∨ (∀z∈t Q(z)) - Free variables and check whether sentence
def ex1_freevars_formula := (rel "R" [var "x", var "y"]) ∨₁ (bV₁ "z" (var "t") (rel "Q" [var "z"]))
#eval Formula.freevars ex1_freevars_formula                         -- The set of free variables is the set {x,y}, that is {"x", "y"}
#eval isClosed_check ex1_freevars_formula                           -- Since ex1_freevars_formula has x and y as free variables, the output is false

-- EXAMPLE 2: Formula R(x,y) - Free variables and check whether sentence
def ex2_freevars_formula := (rel "R" [var "x", var "y"])
#eval Formula.freevars ex2_freevars_formula                         -- The set of free variables is the set {x,y}, that is {"x", "y"}
#eval isClosed_check ex2_freevars_formula                           -- Since ex2_freevars_formula has x and y as free variables, the output is false

-- EXAMPLE 3: Formula ∀z∈t Q(z) - Free variables and check whether sentence
def ex3_freevars_formula := (bV₁ "z" (var "t") (rel "Q" [var "z"]))
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
lemma bExists_base {A : Formula} (x : String) (t : Term) (hA : isBase A) : (isBase (bE₁ x t A)) := by
  unfold bExists
  have h_nA := b_not hA
  have h_unbForall_nA := b_bForall x t h_nA
  exact b_not h_unbForall_nA

-- ------------------
-- EXAMPLE 1.6 (p.14)
-- ------------------

-- Example 1.6.1 (p.14): If B is a base formula, then so is ∀x∈t B(x)
example (B : Formula) (hB_b : isBase B) (x : String) (t : Term): (isBase (bV₁ x t (¬₁ B))) := by
  have H := b_not hB_b
  exact b_bForall x t H

-- Example 1.6.2 (p.14): If A and B are base formulas, then so is ∀x∈t ∃y∈q (A∨B)
example (A B : Formula) (hA_b : isBase A) (hB_b : isBase B) (x y : String) (t q : Term): (isBase (bV₁ x t (bE₁ y q (A ∨₁ B)))) := by
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
| (V₁ y A) => if x = y then V₁ y A
              else V₁ y (substitution_formula x replacement A)
| (bV₁ y t A) => if x = y then bV₁ y t A
              else (bV₁ y t (substitution_formula x replacement A))

-- TESTE daqui ( )
--example : substitution_formula b ((Term.var "x")·(Term.var "y")) A := by sorry
--example (x : String) (t : Term) (A : Formula) : (substitution_formula x t A) := by sorry
def ex0_subst (A:Formula) : Formula :=
    A

def ex00_subst (x : String) (t : Term) (A:Formula) : Formula :=
    substitution_formula x t A
-- até aqui

-- EXAMPLES: formula substitution           -- TODO: falta o repr para podermos ter estes examplos com #eval

-- Example 1:
--#eval substitution_formula "x" Π₁ (rel "R" [var "x", var "y"])        -- gives rel "R" [Π₁, Term.var "y"]

/-
-- Example 2:
def ex2_subst : Formula :=
    (¬₁( (var "x")∈₁(var "y") )) ∨₁ ((var "z")=₁(var "w"))

#eval substitution_formula "x" ∪₁ ex2_subst                             -- gives (¬₁(∪₁ ∈₁ (var "y"))) ∨₁ ((var "z")=₁(var "w"))

-- Example 3:
def ex3_subst : Formula :=
  bForall "y" (var "a") ((var "x")=₁(var "y"))

#eval substitution_formula "x" ind_⋃₁ ex3_subst                         -- gives ∀ "y" ∈ (var "a") (ind_⋃₁ =₁ (var "y"))

-/






-- --------------------------------------
-- --------------------------------------
-- ------------- AXIOMS -----------------
-- --------------------------------------
-- --------------------------------------

--def normal_form (A B : Formula) (x: String) : Formula → Formula
--| or A B => A
--| bForall x A => A
--| t => t

-- Drei strescher ass gleich, wees net wei dat heescht, syntactic equality
inductive Equivalent : Formula → Formula → Prop
| id : Equivalent A A
| comm : Equivalent A B → Equivalent B A
| double_neg : Equivalent (¬₁(¬₁A)) A
| comm_or : Equivalent (A∨₁B) (B∨₁A)                              -- TODO: the same with other obvious stuff
--| nf_left : Equivalent A B → Equivalent (normal_form A) B
--| nf_right : Equivalent A B → Equivalent A (normal_form B)

-- ---------------------------------------------------------------------------------
-- -------------------------------   AXIOMATIC   -----------------------------------
-- ---------------------------------------------------------------------------------

-- Reunião: acrescentar construtor para dizer que tem ou não freevars

/- ISTO
inductive Logic
| PL
| PL_bAC
-/

--ISTO inductive isTrue {L:Logic} : Formula → Prop
inductive isTrue : Formula → Prop
-- AXIOM SCHEMA (Shoenfield)
| lem :                                       -- A ∨ (¬A)
      isTrue (A ∨₁ (¬₁A))
| substitution {t:Term} {x:String} :          -- ∀x A(x) → A(t)
       --x ∈ xs →
       --closed_under_formula A xs →
       x ∈ A.freevars →
       isTrue (.unbForall x A) →
       --------------
       isTrue (substitution_formula x t A)

-- INFERENCE RULES (Shoenfield)
| expansion:                                  -- A => A∨B
      isTrue A →
      ---------------
      isTrue (A ∨₁ B)
| contraction :                               -- A∨A => A
      isTrue (A ∨₁ A) →
      ---------------
      isTrue A
| associativity :                             -- A∨(B∨C) => (A∨B)∨C
      isTrue (A ∨₁ (B ∨₁ C)) →
      ---------------
      isTrue ((A ∨₁ B) ∨₁ C)
| cut :                                       -- A∨B, (¬A)∨C => B∨C
      isTrue (A ∨₁ B) →
      isTrue ((¬₁A)∨₁C) →
      ---------------
      isTrue (B ∨₁ C)
| forall_introduction:                        -- A(x) ∨ B => ∀x A(x) ∨ B
      x ∈ A.freevars →
      isTrue (A ∨₁ B) →
      x ∉ B.freevars →                        -- provided that x does not occur free in B
      ---------------
      isTrue ((unbForall x A) ∨₁ B)

-- OTHER AXIOMS
| equivalence :
      (Equivalent A B) →
      isTrue A →
      isTrue B
| AxE₁ (x : String) :
    isTrue ((var x) =₁ (var x))
-- Problema yes: falta A(x) e A(y) -> criar notação?
--| AxE₂ (x y : String) (A : Formula) (h : x ∈ A.freevars): isTrue ((((var x) =₁ (var y))∧₁A) →₁ B) ∧ (y ∈ A.freevars)
--| AxE₂ (x y : String) : isTrue ((((var x) =₁ (var y))∧₁ A) →₁ A)        FALTA: falta x=y ∧ A(x) → A[substituition](y)
| Teste (x y : String) (A B : Formula) (h: x ∈ A.freevars) (Hy : y∉A.freevars) (HB : B = (substitution_formula x (var y) A)): isTrue ((((var x) =₁ (var y))∧₁A) →₁ B)
| AxU (x : String) (t : Term) (A : Formula) :
    isTrue ((bV₁ x t A) ↔₁ (V₁ x (((var x) ∈₁ t) →₁ A)))
| AxC₁ (t₁ t₂ : Term) :                                         -- TODO: mudar isto tudo para variables em vez de terms
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
| AxS₃ (a f b : Term) : isTrue ((b ∈₁ ((ind_⋃₁·a)·f)) ↔₁ (bE₁ x a (b ∈₁ (f·(var x)))))
| bAC {x y f : String} : isTrue ((V₁ x (E₁ y A)) →₁ (E₁ f (V₁ x (bE₁ y ((Term.var f)·(Term.var x)) A))))    -- bAC^ω_*
-- ISTO | bAC {x y f : String} {H:L=Logic.PL_bAC}: isTrue ((V₁ x (E₁ y A)) →₁ (E₁ f (V₁ x (bE₁ y ((Term.var f)·(Term.var x)) A))))    -- bAC^ω_*
-- Sempre que for para usar o isTrue é preciso escolher a lógica!

-- TESTE: o lemma eq_symmetry está a dar erro, mas o teste com #check mostra que a sintaxe está good
def f : Term := var "f"
def g : Term := var "g"

#check (f =₁ g) →₁ (g =₁ f)

-- Problema: this ↓ is not working
--lemma eq_symmetry (p q : Term): (p =₁ q) := sorry
lemma eq_symmetry : ∀(p q:Term), isTrue ((p=₁q)→₁(q=₁p)) := sorry -- construtores de isTrue
-- ISTO lemma eq_symmetry : ∀(p q:Term), isTrue (L := Logic.PL) ((p=₁q)→₁(q=₁p)) := sorry -- construtores de isTrue

--theorem tastino (x y : String) : Formula

--lemma eq_symmetry (x y : String) : (((var x) =₁ (var y)) →₁ ((var y) =₁ (var x))) := sorry

--lemma eq_transitivity (x y z : String) : ((((var x) =₁ (var y)) ∧₁ ((var y) =₁ (var z))) →₁ ((var x) =₁ (var z))) := sorry


-- -------------------------------------------------------------------------------------
-- -------------------------------------------------------------------------------------

-- ----------------------------------------------------
-- ------------ COMBINATORIAL COMPLETENESS ------------ (Section 1.2.4)
-- ----------------------------------------------------

theorem combinatorial_completeness (x : String) : ∀(t:Term), ∃(q:Term), ∀(s:Term),
  isTrue ((q·s) =₁ (term_substitution x s t)) :=
  -- ISTO isTrue (L := Logic.PL) ((q·s) =₁ (term_substitution x s t)) :=
by
  intro t
  have t₂ := t
  cases t with                                     -- TO DO: AQUI como fazer os meus cases? ver def 1.11
  | var y =>
      by_cases h: x = y
      . existsi ((Σ₁·Π₁)·Π₁)
        intro s
        unfold term_substitution
        rewrite [h]
        simp
        have H1 := isTrue.AxC₁ s (Π₁·s)
        have H2 := isTrue.AxC₂ Π₁ Π₁ s
        --ISTO have H1 := isTrue.AxC₁ (L := Logic.PL) s (Π₁·s)
        --ISTO have H2 := isTrue.AxC₂ (L := Logic.PL) Π₁ Π₁ s    -- usar simetria/transitivity da igualdade
        sorry
      . existsi (Π₁·(var y))
        intro s
        rewrite [term_substitution]
        rewrite [if_neg h]
        exact isTrue.AxC₁ (var y) s
          --match y with
            --| x => intro ((Σ₁·Π₁)·Π₁)
            --| _ => var y
            --sorry --intro ((Σ₁·Π₁)·Π₁) FAZER PATTERNMATCH
  | _ =>
      by_cases h: x∈ t₂.freevars
      . sorry         -- same as
      . existsi (Π₁·t₂)           -- TODO: vai precisar de lemas auxiliares (se a variavel não esta nas freevars, não muda nada na substituiçao)
        intro s
        unfold term_substitution
        --rewrite [if_neg h]
        --exact isTrue.AxC₁ (var y) s
        sorry


inductive lambda : Type
| la (s : String) (body : Term): lambda

def lambda.to_term : lambda → Term
| .la x (var y) => if x=y then ((Σ₁·Π₁)·Π₁) else (Π₁·(var y))
| .la x (t·s) => if x∉(t·s).freevars then (Π₁·t) else ((Σ₁·(lambda.la x t).to_term)·(lambda.la x s).to_term)
| .la x t => if x∉t.freevars then (Π₁·t) else (by sorry) -- Reunião: do pattermatching por extenso com as constantes

-- Problema: how to deal with this?
theorem combinatorial_completeness2 (x : String) : ∀(t:Term), ∃(q:Term), ∀(s:Term),
  isTrue ((q·s) =₁ (term_substitution x s t)) :=
  --ISTO isTrue (L := Logic.PL) ((q·s) =₁ (term_substitution x s t)) :=
by
  intro t
  have t₂ := t -- Reunião: é preciso tirar isto para reconstruir à mão
  cases t with
  | var y =>                              -- CASO 1: t é uma variável
      by_cases h: x = y
      . existsi ((Σ₁·Π₁)·Π₁)              --  Caso 1a: t é a variável x
        intro s
        unfold term_substitution
        rewrite [h]
        simp
        have H1 := isTrue.AxC₁ s (Π₁·s)
        have H2 := isTrue.AxC₂ Π₁ Π₁ s
        --ISTO have H1 := isTrue.AxC₁ (L := Logic.PL) s (Π₁·s)
        --ISTO have H2 := isTrue.AxC₂ (L := Logic.PL) Π₁ Π₁ s        -- usar simetria/transitivity da igualdade
                                              -- acho que precisamos de extensionality de isTrue
        sorry
      . existsi (Π₁·(var y))              --  Caso 1b: t não é a variável x
        intro s
        rewrite [term_substitution]
        rewrite [if_neg h]                -- porque x ≠ y (hipótese h), logo dá var y
        exact isTrue.AxC₁ (var y) s
        -- ISTO exact isTrue.AxC₁ (L := Logic.PL) (var y) s
  | _ =>     -- Reunião: temos de fazer todos os casos das constantes                           -- CASO 2: t não é uma variável, é outra coisa (constante ou aplicação)
      sorry
      /-
      by_cases h: x∈ t₂.freevars          --         dois casos: t não tem x (x does not occur in t) OU t tem x (e é aplicação)
      . sorry
      . existsi (Π₁·t₂)
        intro s
        unfold term_substitution
        induction s
        . rename_i b
          --rename_i a
          have d := isTrue.AxC₁ t₂
          --have r1 : t₂ = lcons (LTerm.Lsubstitution x b a) := by sorry
          --apply d
          sorry
      -/



-- (λx.t)s = s[t/x] = q·s
-- (λx.t) -> existsi (Σ₁·(λx.t))·(λx.q)

--def term_substitution (x : String) (replacement : Term) : Term → Term


-- TO DO: precisamos de conseguir dizer "Consider t(x), where x is a variable of t"
-- chega dizer x ∈ t.allvars ?

-- TO DO: notação para A(x) se A:Formula e x ∈ A.allvars ?
-- Problema yes: preciso que isto seja uma Formula

example : {F:Formula // {"x","y"} ⊆ F.allvars} → Prop := by sorry


-- REMARK 1.14: Every type is inhabited by at least one term (TODO)




-- ----------------------------------------------------
-- ------------------- CONVERSIONS -------------------- (Section 1.2.5)
-- ----------------------------------------------------

-- Definition 1.14 (Conversions)
@[simp]
def conv : Term → Term
| ((Π₁·t₁)·t₂) => t₁
| (((Σ₁·t₁)·t₂)·t₃) => ((t₁·t₃)·(t₂·t₃))
| ((ind_⋃₁·(𝔰₁·t₁))·t₂) => (t₂·t₁)
| ((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) => ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃))
| t => t


notation t "▹" => conv t

-- Checks whether a term converts to another one
inductive ConvertsTo : Term → Term → Prop
| c1_pi (t₁ t₂): ConvertsTo ((Π₁·t₁)·t₂) t₁
| c2_sigma (t₁ t₂ t₃): ConvertsTo (((Σ₁·t₁)·t₂)·t₃) ((t₁·t₃)·(t₂·t₃))
| c3_indU (t₁ t₂) : ConvertsTo ((ind_⋃₁·(𝔰₁·t₁))·t₂) (t₂·t₁)
| c4_indU_binU (t₁ t₂ t₃): ConvertsTo ((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃))

def ConvertsTo_check (t₁ t₂ : Term): Bool := if conv t₁ = t₂ then true else false


-- EXAMPLE: using conv to convert ((Π₁·p₁)·p₂) to p₁ for terms p₁ p₂
--          and using ConvertsTo_check to check whether a term converts to another term

def ex_conv (q t : Term) := ((Π₁·q)·t)

def p₁ : Term := var "p₁"
def p₂ : Term := var "p₂"

#eval ex_conv p₁ p₂                         -- evaluates to (Π₁·p₁)·p₂
#eval conv ((Π₁·p₁)·p₂)                     -- evaluates to p₁ (i.e. (Π₁·p₁)·p₂ converts to p₁)
#eval ((Π₁·p₁)·p₂) ▹                        -- evaluates to p₁ (i.e. (Π₁·p₁)·p₂ converts to p₁)

#eval ConvertsTo_check ((Π₁·p₁)·p₂) p₁      -- true: the term (Π₁·p₁)·p₂ converts to p₁
#eval ConvertsTo_check ((Π₁·p₁)·p₂) p₂      -- false: the term (Π₁·p₁)·p₂ does not convert to p₁


-- --------------------------
-- Conversions preserve types
-- --------------------------

-- ---------------------
-- REMARK 1.21 (p.26):
-- Conversions preserve types
-- ---------------------


lemma Conv1_TypeChecking (σ τ : FType) (t₁ t₂ : Term) (ht₁ : Term_TypeChecking t₁ σ) (ht₂ : Term_TypeChecking t₂ τ) : Term_TypeChecking (conv ((Π₁·t₁)·t₂)) σ := by
  --exact ht₁
  --let H : Term := conv ((Π₁·t₁)·t₂)
  have H2 : conv ((Π₁·t₁)·t₂) = t₁ := by simp [conv]              -- Ter o resultado da conv as a new assumption
  rw [H2]
  exact ht₁


lemma Conv2_TypeChecking (σ τ ρ : FType) (t₁ t₂ t₃ : Term) (ht₁ : Term_TypeChecking t₁ (ρ ⟶ σ ⟶ τ)) (ht₂ : Term_TypeChecking t₂ (ρ ⟶ σ)) (ht₃ : Term_TypeChecking t₃ ρ) : Term_TypeChecking (conv ((Σ₁·t₁)·t₂)·t₃) τ := sorry

-- MANUALMENTE:

-- TODO not now: mudar hPi? not needed? Mudar Term_Checking.tcPi de {σ τ} para (σ τ : FType) ?

-- Conversion 1 preserves types - ((Π₁·t₁)·t₂) ▹ t₁
example (σ τ : FType) (t₁ t₂ : Term)
    (ht₁ : Term_TypeChecking t₁ σ)
    (ht₂ : Term_TypeChecking t₂ τ)
    (hPi : Term_TypeChecking Π₁ (σ ⟶ τ ⟶ σ)) : Term_TypeChecking ((Π₁·t₁)·t₂) σ :=
  by
    have H := Term_TypeChecking.tcApp hPi ht₁
    exact Term_TypeChecking.tcApp H ht₂

-- Conversion 2 preserves types - (((Σ₁·t₁)·t₂)·t₃) ▹ ((t₁·t₃)·(t₂·t₃))
example (σ τ ρ : FType) (t₁ t₂ t₃ : Term)
    (ht₁ : Term_TypeChecking t₁ (σ ⟶ (τ ⟶ ρ)))
    (ht₂ : Term_TypeChecking t₂ (σ ⟶ τ))
    (ht₃ : Term_TypeChecking t₃ σ) : Term_TypeChecking ((t₁·t₃)·(t₂·t₃)) ρ :=
  by
    have H1 := Term_TypeChecking.tcApp ht₁ ht₃
    have H2 := Term_TypeChecking.tcApp ht₂ ht₃
    exact Term_TypeChecking.tcApp H1 H2

example (σ τ ρ : FType) (t₁ t₂ t₃ : Term)
    (ht₁ : Term_TypeChecking t₁ (σ ⟶ (τ ⟶ ρ)))
    (ht₂ : Term_TypeChecking t₂ (σ ⟶ τ))
    (ht₃ : Term_TypeChecking t₃ σ)
    (hSigma : Term_TypeChecking Σ₁ ((σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ)))) : Term_TypeChecking (((Σ₁·t₁)·t₂)·t₃) ρ :=
  by
    have H1 := Term_TypeChecking.tcApp hSigma ht₁
    have H2 := Term_TypeChecking.tcApp H1 ht₂
    exact Term_TypeChecking.tcApp H2 ht₃

-- Conversion 3 preserves types - (((ind_⋃₁·(𝔰₁·t₁))·t₂)) ▹ (t₂·t₁)
example (σ τ : FType) (t₁ t₂ : Term)
    (ht₁ : Term_TypeChecking t₁ σ)
    (ht₂ : Term_TypeChecking t₂ (σ ⟶ τ⋆))
    (hSing : Term_TypeChecking 𝔰₁ (σ ⟶ σ⋆))
    (hIUnion : Term_TypeChecking ind_⋃₁ (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆))) : Term_TypeChecking ((ind_⋃₁·(𝔰₁·t₁))·t₂) (τ⋆) :=
  by
    have H1 := Term_TypeChecking.tcApp hSing ht₁
    have H2 := Term_TypeChecking.tcApp hIUnion H1
    exact Term_TypeChecking.tcApp H2 ht₂

example (σ τ : FType) (t₁ t₂ : Term)
    (ht₁ : Term_TypeChecking t₁ σ)
    (ht₂ : Term_TypeChecking t₂ (σ ⟶ (τ⋆))) : Term_TypeChecking (t₂·t₁) (τ⋆) :=
  by
    exact Term_TypeChecking.tcApp ht₂ ht₁

-- Conversion 4 preserves types - ((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) ▹ ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃))
example (σ τ : FType) (t₁ t₂ t₃: Term)
    (ht₁ : Term_TypeChecking t₁ (σ⋆))
    (ht₂ : Term_TypeChecking t₂ (σ⋆))
    (ht₃ : Term_TypeChecking t₃ (σ ⟶ τ⋆))
    (hBUnion : Term_TypeChecking ∪₁ (σ⋆ ⟶ σ⋆ ⟶ σ⋆))
    (hIUnion : Term_TypeChecking ind_⋃₁ (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆))) : Term_TypeChecking ((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) (τ⋆) :=
  by
    have H1 := Term_TypeChecking.tcApp (Term_TypeChecking.tcApp hBUnion ht₁) ht₂
    exact Term_TypeChecking.tcApp (Term_TypeChecking.tcApp hIUnion H1) ht₃

example (σ τ : FType) (t₁ t₂ t₃: Term)
    (ht₁ : Term_TypeChecking t₁ (σ⋆))
    (ht₂ : Term_TypeChecking t₂ (σ⋆))
    (ht₃ : Term_TypeChecking t₃ (σ ⟶ τ⋆))
    (hBUnion : Term_TypeChecking ∪₁ (τ⋆ ⟶ τ⋆ ⟶ τ⋆))
    (hIUnion : Term_TypeChecking ind_⋃₁ (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆))) : Term_TypeChecking ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)) (τ⋆) :=
  by
    have H1 := Term_TypeChecking.tcApp (Term_TypeChecking.tcApp hIUnion ht₁) ht₃
    have H2 := Term_TypeChecking.tcApp (Term_TypeChecking.tcApp hIUnion ht₂) ht₃
    exact Term_TypeChecking.tcApp (Term_TypeChecking.tcApp hBUnion H1) H2

/-
CINCO TENTATIVAS PARA CONVERSIONS PRESERVE TYPES

inductive Conv_TypeChecking : Term → FType → Prop                 -- Definir um Conv_TypeChecking?
| tcConv1
| tcConv2
| tcConv3
| tcConv4

lemma conv1_preserves_types (t t' : Term) (σ τ ρ ρ' : FType)
                            (ht₁ : Term_TypeChecking t₁ σ)
                            (ht₂ : Term_TypeChecking t₂ τ)
                            (hPi : Term_TypeChecking Π₁ (σ ⟶ τ ⟶ σ))
                            (H : Term_TypeChecking ((Π₁·t₁)·t₂) ρ) :
    Term_TypeChecking t₁ ρ :=
by
  have H1 := Term_TypeChecking.tcApp hPi ht₁
  have H2 := Term_TypeChecking.tcApp H1 ht₂
  have H3 := ((Π₁·t₁)·t₂)

lemma conv1_preserves_types :
  (t₁ t₂ : Term) (σ τ ρ ρ' : FType) (ht₁ : Term_TypeChecking t₁ σ) (ht₂ : Term_TypeChecking t₂ τ),
    Term_TypeChecking ((Π₁·t₁)·t₂) ρ →
    Term_TypeChecking t₁ ρ' →
    ρ = ρ' := by sorry

lemma conv_preserve_types :
  (t₁ t₂ : Term) (σ : FType),
    ConvertsTo t₁ t₂ →
    Term_TypeChecking t₁ σ →
    Term_TypeChecking t₂ τ →
    σ = τ := by sorry
-/

--Auxiliary lemma: Every term has exactly one type TODO
lemma Type_Uniqueness {t : Term} {σ τ : FType} :
  Term_TypeChecking t σ →
  Term_TypeChecking t τ →
  σ = τ := by sorry
  /-                              -- Reunião / se não funcionar => induction no tipo ou termo
  intro tc1 tc2
  induction t                       -- Do livro da reunião que sugere induction on the term
  . cases tc1
    cases tc2
    rfl
  . sorry                           -- Problema: dois Π's diferentes não têm de ter os mesmos tipos
  --  cases tc1
  --  cases tc2
  . sorry
  . sorry
  -/


-- Conversion 1 preserves types - ((Π₁·t₁)·t₂) ▹ t₁
lemma xx {σ τ : FType} {t₁ t₂ : Term}
    (ht₁ : Term_TypeChecking t₁ σ)
    (ht₂ : Term_TypeChecking t₂ τ)
    (hPi : Term_TypeChecking Π₁ (σ ⟶ τ ⟶ σ)) : Term_TypeChecking ((Π₁·t₁)·t₂) σ :=
  by
    have H := Term_TypeChecking.tcApp hPi ht₁
    exact Term_TypeChecking.tcApp H ht₂

-- ---------------
-- Inversion lemma      TODO: tentar fazer o global antes dos pequenos
-- ---------------

-- LEMMA: Inversion lemma       -- TODO: o livro
/-
lemma inv_lemma1 {t₁ t₂ t₃ : Term} {σ τ : FType} :
    (Term_TypeChecking ((Π₁·t₁)·t₂) σ) →
    (Term_TypeCheking (Π₁·t₁) τ) →
    ((Term_TypeCheking (t₁) σ) ∧ (Term_TypeCheking t₂ τ)) := by sorry
-/

lemma inv_lemma_app_right {t₁ t₂ : Term} {σ τ : FType} :        -- TO DO: does this look right?
    (Term_TypeChecking (t₁·t₂) τ) →
    (Term_TypeChecking t₁ (σ⟶τ)) →
    (Term_TypeChecking t₂ σ) := by
    intro h1 h2
    cases t₂ with
    | lcons _ => sorry
    /- mien
        rename_i t
        cases σ
        have H := tcLcons t
        exact H
    -/
    | pi => sorry
    | sigma => sorry
    | sing => sorry
    | bUnion => sorry
    | iUnion => sorry
    | var _ => sorry
    | app _ _ => sorry


lemma inv_lemma_app_left {t₁ t₂ : Term} {σ τ : FType} :
    (Term_TypeChecking (t₁·t₂) τ) →
    (Term_TypeChecking t₂ σ) →
    (Term_TypeChecking t₁ (σ⟶τ)) := by sorry
    --intro h1 h2

lemma inv_lemma_pi {t₁ t₂ : Term} {σ τ : FType} :
    ((Term_TypeChecking ((Π₁·t₁)·t₂) σ) → ((Term_TypeChecking t₁ σ) ∧ (Term_TypeChecking t₂ τ))) := by sorry

-- lemma inv_lemma_sigma

-- --------------------------
-- Conversions preserve types
-- --------------------------

-- LEMMA: Conversions preserve types
lemma conversions_preserve_types {t₁ t₂ : Term} {σ τ : FType} :     -- Para que cases seja para inductive def de conversions -> induction nessa hipotese
    ConvertsTo t₁ t₂ →
    Term_TypeChecking t₁ σ →
    Term_TypeChecking t₂ τ →
    σ = τ := by
    intro ct tc1 tc2                              -- ct (ConvertsTo hypothesis), tc1 tc2 (Term_TypeChecking hypothesis)
    induction ct with                             -- induction on the hypothesis ConvertsTo
    | c1_pi t₁ t₂ => sorry
      /-
      cases tc1                                   -- Reunião
      rename_i t₃ t₄ ρ tc_t₂ tc_pi
      have y := xx tc2 tc_t₂ Term_TypeChecking.tcPi
      have H2 : t₁ = conv ((Π₁·t₁)·t₂) := by simp [conv]        -- usar isTrue aqui para depois poder rw? (thinking)
      rw [H2] at tc2
      -/

      -- fazer rewrite e depois usar Type_Uniqueness

        -- TODO: versão manual different, here não sabemos o tipo de t₂
        --2match tc1 with
        --2| tcApp _ _ (tcApp _ _ tcPi _) _ => rfl
        --2| _ => by_contra
        --let H : (conv (((Π₁·t₁)·t₂)) = t₁) := by simp [conv]
        --1 let H : ((conv ((Π₁·t₁)·t₂)) = t₁) := by simp [conv]
        --1 in
        --1 match tc1, H with
        --let T := conv ((Π₁·t₁)·t₂)
        --have H : (T = t₁) := by exact rfl
        --sorry
        --refine Type_Uniqueness _ σ τ ?c1_pi.a _
    | c2_sigma t₁ t₂ t₃ => sorry
    | c3_indU t₁ t₂ => sorry
        --let H : ((ind_⋃₁·𝔰₁·t₁)·t₂) ▹ (t₂·t₁) := by simp [conv]
        --in
        --match tc1, H with
        --| Term_TypeChecking.tcApp _ _ (Term_TypeChecking.tcApp _ _ Term_TypeChecking.tcIUnion _), _ =>
      -- Using type-checking information
        --have : σ = τ :=
        --match tc2 with
      --| _ => rfl
      --exact this
    | c4_indU_binU t₁ t₂ t₃ => sorry

inductive ReducesTo : Term → Term → Prop
| reflex (t) : ReducesTo t t                                                -- A term reduces to itself
| app_left {t₁ t₂ t₁'} : ReducesTo t₁ t₁' → ReducesTo (t₁·t₂) (t₁'·t₂)      -- Reduction in the left subterm of an application
| app_right {t₁ t₂ t₂'} : ReducesTo t₂ t₂' → ReducesTo (t₁·t₂) (t₁·t₂')     -- Reduction in the right subterm of an application
| one_step {t₁ t₂} : ConvertsTo t₁ t₂ → ReducesTo t₁ t₂
| n_step {t₁ t₂ t₃} : ReducesTo t₁ t₂ → ReducesTo t₂ t₃ → ReducesTo t₁ t₃   -- Transitivity to represent n-step reductions

open ReducesTo

-- Example: Conversions are one-step reductions (example with C1 conversion)
example (t₁ t₂ : Term) : ReducesTo ((Π₁·t₁)·t₂) t₁ :=
  by
    have H1 := ConvertsTo.c1_pi t₁ t₂
    exact ReducesTo.one_step H1


--def ReducesTo_check (t₁ t₂ : Term): Bool := if ((ReducesTo t₁ t₂) = true) then true else false

-- TODO: isRedex, isReduct, isReducible (definition 1.15, p.27)

/- TODO: Normalizar até não funcionar mais -> TODO yes: precisa de decreasing?
def normalize (t : Term) : Term :=
  let t' := conv t
  if t = t' then t
  else normalize t'
-/


-- ---------------------------------------------
-- REMARK 1.23 (p.28): Reductions preserve types
-- ---------------------------------------------

-- LEMMA: Reductions preserve types
lemma reductions_preserve_types {t₁ t₂ : Term} {σ τ : FType} :     -- TODO now: yes: problema -> o cases devia ser para inductive def de conversions
    ReducesTo t₁ t₂ →
    Term_TypeChecking t₁ σ →
    Term_TypeChecking t₂ τ →
    σ = τ := by
    intro red_t tc1 tc2
    induction red_t with
    | reflex t => exact Type_Uniqueness tc1 tc2
    | app_left rd tc => sorry
    | app_right rd tc => sorry
    | one_step h_ct => exact (conversions_preserve_types h_ct tc1 tc2)       -- TODO: como rename as metavariables com as cruzes?
    | n_step h_red_t1t2 h_red_t2t3 h_type_un_t1t2 h_type_un_t2t3 => sorry     -- Looking good, keep on doing this
        --have h_red_t1t3 := ReducesTo.n_step h_red_t1t2 h_red_t2t3
        --have H := h_type_un_t1t2 tc1


-- ----------------------------------------------
-- DEFINITION 1.16 (p.28): "Reduction sequences"
-- ----------------------------------------------

inductive steps_into : ℕ → Term → Term → Prop
| single : steps_into 1 t (conv t)
| multiple : steps_into n t₁ t₂ → steps_into m t₂ t₃ → steps_into (n+m) t₁ t₃

/-
-- TO DO: pq não funciona? Termination & Decreasing?      IGNORE
def count_steps : Term → Term → ℕ
| t₁, t₂ => if t₁ = t₂ then 0
           else (1 + (count_steps (conv t₁) t₂))
-/


-- ------------------------------------------
-- EXAMPLE 1.10 (p.28): Example of reductions
-- ------------------------------------------

lemma Ex1_10_1 (t₁ t₂ t₃ : Term) : ReducesTo ((Σ₁·t₁)·((Π₁·t₂)·t₃)) ((Σ₁·t₁)·t₂) :=
by
  have H1 := ConvertsTo.c1_pi t₂ t₃
  have H2 := ReducesTo.one_step H1
  exact @ReducesTo.app_right (Σ₁·t₁) ((Π₁·t₂)·t₃) t₂ H2               -- @ permite inserir os argumentos implícitos

lemma Ex1_10_2 (t₁ t₂ t₃ : Term) : ReducesTo (((ind_⋃₁·(𝔰₁·t₁))·t₂)·t₃) ((t₂·t₁)·t₃) :=
by
  have H1 := ConvertsTo.c3_indU t₁ t₂
  have H2 := ReducesTo.one_step H1
  exact @ReducesTo.app_left ((ind_⋃₁·(𝔰₁·t₁))·t₂) t₃ (t₂·t₁) H2

lemma Ex1_10_3 (t q r : Term) : ReducesTo ((ind_⋃₁·((∪₁·(𝔰₁·t))·q))·r) ((∪₁·(r·t))·((ind_⋃₁·q)·r)) :=
by
  have H1 := ConvertsTo.c4_indU_binU (𝔰₁·t) q r
  have H2 := ReducesTo.one_step H1
  have H3 := ConvertsTo.c3_indU t r
  have H4 := ReducesTo.one_step H3
  have H5 := @ReducesTo.app_right ∪₁ ((ind_⋃₁·(𝔰₁·t))·r) (r·t) H4
  have H6 := @ReducesTo.app_left (∪₁·((ind_⋃₁·(𝔰₁·t))·r)) ((ind_⋃₁·q)·r) (∪₁·(r·t)) H5
  exact ReducesTo.n_step H2 H6

-- ----------------------------------------------------------------------
-- EXAMPLE 1.11 (p.29): Example of different possible reduction sequences
-- ----------------------------------------------------------------------

lemma Ex1_11_Seq1 (r q t s : Term) : ReducesTo (((Σ₁·r)·((Π₁·q)·t))·s) ((r·s)·(q·s)) :=
by
  have H1 := ConvertsTo.c1_pi q t
  have H2 := ReducesTo.one_step H1
  have H3 := ConvertsTo.c2_sigma r q s
  have H4 := ReducesTo.one_step H3
  have H5 := @ReducesTo.app_right (Σ₁·r) ((Π₁·q)·t) q H2
  have H6 := @ReducesTo.app_left ((Σ₁·r)·((Π₁·q)·t)) s ((Σ₁·r)·q) H5
  exact ReducesTo.n_step H6 H4

lemma Ex1_11_Seq2 (r q t s : Term) : ReducesTo (((Σ₁·r)·((Π₁·q)·t))·s) ((r·s)·(q·s)) :=
by
  have H1 := ConvertsTo.c2_sigma r ((Π₁·q)·t) s
  have H2 := ReducesTo.one_step H1
  have H3 := ConvertsTo.c1_pi q t
  have H4 := ReducesTo.one_step H3
  have H5 := @ReducesTo.app_left ((Π₁·q)·t) s q H4
  have H6 := @ReducesTo.app_right (r·s) (((Π₁·q)·t)·s) (q·s) H5
  exact ReducesTo.n_step H2 H6



-- ---------------------
-- Normal form of a term
-- ---------------------

-- DEFINITION: checks whether a term is in normal form
def isNormal : Term → Prop
| t => (conv t = t)                                         -- TODO not now: isto assim não deixa converter subterms
                                                            -- a tirar

@[simp]
def isNormal2 (t:Term): Prop := ∀ t', ReducesTo t t' → t = t'

-- DEFINITION: checks whether a term is in normal form
def isNormal_check : Term → Bool                            -- a tirar, vai ter de ser Prop e não Bool
| t => if conv t = t then true else false

-- DEFINITION: normal form of a term
def normal_form (t : Term) : Term :=
if (isNormal_check t) = true then t else conv t

-- Ex1_10_1: ((Σ₁·t₁)·((Π₁·t₂)·t₃)) reduces to ((Σ₁·t₁)·t₂)
def example_term_Ex1_10_1_A := ((Σ₁·(var "t₁"))·((Π₁·(var "t₂"))·(var "t₃")))
def example_term_Ex1_10_1_B := ((Σ₁·(var "t₁"))·(var "t₂"))

#eval example_term_Ex1_10_1_A
#eval conv example_term_Ex1_10_1_A

#eval isNormal_check example_term_Ex1_10_1_A              -- TODO: not working, diz que é Normal mas não é
#eval isNormal_check example_term_Ex1_10_1_B

/-
example : isNormal2 example_term_Ex1_10_1_B := by         -- TODO (future); might need additional lemmas
  unfold example_term_Ex1_10_1_B
  unfold isNormal2
  intro x rt
  cases rt with
  | reflex t => exact rfl
  | app_left _ => sorry
  | app_right _ => sorry
  | one_step h => cases h
  | n_step h1 h2 => cases h1 <;> cases h2 <;> simp <;> rfl
                    . rename_i a b                        -- . para ir só para o primeiro goal
                      cases b with
                      | reflex t => sorry
                      | app_left _ => sorry
                      | app_right _ => sorry
                      | one_step _ => sorry
                      | n_step _ _ => sorry
-/

  --cases x <;> cases rt    -> fazer todos os goals

-- Example: using Ex1_11_Seq2 to see that ((Σ₁·r)·((Π₁·q)·t))·s is not normal, while (r·s)·(q·s) is
--          we will consider the terms to be variables (using the above term names for the strings).

def example_term_Ex1_11_Seq2_A := (((Σ₁·(var "r"))·((Π₁·(var "q"))·(var "t")))·(var "s"))
def example_term_Ex1_11_Seq2_B := (((var "r")·(var "s"))·((var "q")·(var "s")))

#eval isNormal_check example_term_Ex1_11_Seq2_A           -- Output is false since ((Σ₁·r)·((Π₁·q)·t))·s is not normal
#eval isNormal_check example_term_Ex1_11_Seq2_B           -- Output is true since (r·s)·(q·s) is not normal

#eval normal_form example_term_Ex1_11_Seq2_A              -- TODO: not working -> problem with subterms?


-- TODO: isNormalizable, isStronglyNormalizable
-- TODO yes: How to define finite reduction sequences and strongly normalizable? (def 1.17, p.30)
        -- Use ∃n natural e stepsinto

-- TODO yes: Lemas e teoremas sem demo na dissertação (p.32/33)
--        Newman's lemma, SN property, CR property -> how to avoid aviso? don't avoid it, leave sorry




-- ---------------------------------------------------------------------------------------------------------------
--             SECTION 1.2.6: Characterization of closed normal terms
-- ---------------------------------------------------------------------------------------------------------------

-- ---------------------------------------------------------
-- REMARK 1.30 (p.32):
-- General form of closed terms -> fazer cases on constants?
-- ---------------------------------------------------------


-- ---------------------------------------------------------
-- REMARK 1.31 (p.33):
-- General form of closed normal terms -> fazer cases on constants?
-- ---------------------------------------------------------

-- ---------------------------------------------------------
-- PROPOSITION 1.3 (p.33): Ground normal form
-- ---------------------------------------------------------

-- TO DO: Falta dizer que é ground
lemma GroundNormalForm (t : Term) (tL : LTerm) (h1 : t.isClosedTerm) (h2 : isNormal t) : (t = Term.lcons tL) :=
  by sorry

-- ---------------------------------------------------------
-- DEFINITION 1.19 (p.36):
-- set-like terms   --> needs isSetLike
-- ---------------------------------------------------------



-- Problema: how to define isSetLike?
/-
def isSetLike (t : Term) : Prop := isSing ∨ isbUnion ∨ both
-/

def Term.isPartialSetLike : Term → Prop
| .lcons _
| pi                                 -- combinators:     Π
| sigma => false                               --                  Σ
| sing                                   -- star constants:  𝔰
| bUnion => true                                --                  ∪ (binary union)
| iUnion                                 --                  ∪ (indexed union)
| var _ => false                -- variables
| app a b => (a.isPartialSetLike) ∨ (b.isPartialSetLike)

def Term.isSetLike (t:Term) (σ:FType): Prop := t.isPartialSetLike ∧ (Term_TypeChecking t (σ⋆))



-- (h : a.isSetLike) Reunião: precisa de typechecking


-- ---------------------------------------------------------
-- EXAMPLE 1.14 (p.36)
-- ---------------------------------------------------------

/-
TO DO: precisa de isSetLike_check com True/False
-/

def ex1_14_term1 (t : Term) := 𝔰₁·t                             -- true
def ex1_14_term2 (r₁ r₂ : Term) := ((∪₁·r₁)·(𝔰₁·r₂))            -- true
def ex1_14_term3 (p₁ p₂ q₁ q₂ : Term) := (∪₁·(p₁·p₂))·(q₁·q₂)   -- true
def ex1_14_term4 (u₁ u₂ : Term) := 𝔰₁·((ind_⋃₁·u₁)·u₂)          -- true
def ex1_14_term5 (u₁ u₂ : Term) := ((ind_⋃₁·u₁)·u₂)             -- false


-- ---------------------------------------------------------
-- PROPOSITION 1.4 (p.36):
-- Star normal form
-- ---------------------------------------------------------

/- TO DO: falta definir isSetLike
lemma StarNormalForm
  (σ:FType) (t:Term)
  (h1 : t.isClosedTerm) (h2 : isNormal t) (h3 : Term_TypeChecking t σ⋆) :
  (t : isSetLike) := by sorry
-/


-- ---------------------------------------------------------
-- REMARK 1.31 (p.37):
-- Structure of closed normal terms
-- ---------------------------------------------------------

-- ORA ESTA FICA PARA O FIM







-- ---------------------------------------------------------------------------------------------------------------
--                          "PRENEXIFICATION RULES"
-- ---------------------------------------------------------------------------------------------------------------

-- PRENEXIFICATION RULES
-- Definir novo inductive para termos as usual prenexification rules?
-- ou usar um isFormula?

-- FREE VARIABLES NOT WORKING :'(
-- TODO: prenexificação para LFormula

-- TODO: usar numero minimo de prenex rules e o resto def as lemmas com a boa notação

def prenex : Formula → Formula
| .not (Formula.unbForall x A)  => Formula.unbForall x (prenex (Formula.not A))
| .not (Formula.bForall x t A)  => Formula.bForall x t (prenex (Formula.not A))
| Formula.or (Formula.unbForall x A) B => Formula.unbForall x (prenex (Formula.or A B))
| Formula.or (Formula.bForall x t A) B => Formula.bForall x t (prenex (Formula.or A B))
| Formula.or A (Formula.unbForall x B) => Formula.unbForall x (prenex (Formula.or A B))
| Formula.or A (Formula.bForall x t B) => Formula.bForall x t (prenex (Formula.or A B))
| Formula.unbForall x A => Formula.unbForall x (prenex A)
| Formula.bForall x t A => Formula.bForall x t (prenex A)
| Formula.rel r l_term => Formula.rel r l_term
| Formula.eq t₁ t₂ => Formula.eq t₁ t₂
| Formula.mem t₁ t₂ => Formula.mem t₁ t₂
| Formula.not A => Formula.not (prenex A)
| Formula.or A B => Formula.or (prenex A) (prenex B)
| x => x

/- LOOKING GOOD, but falar de freevars?

lemma DM1 (A B : Formula) : (¬₁(A∨₁B)) = ((¬₁A)∧₁(¬₁B)) := by sorry

lemma DM2 (A B : Formula) : (¬₁(A∧₁B)) = ((¬₁A)∨₁(¬₁B)) := by sorry

-----------

lemma Prenex1 (x y : String) (A : Formula) : (E₁ x (E₁ y A)) = (E₁ y (E₁ x A)) := by sorry

lemma Prenex2 (x y : String) (t : Term) (A : Formula) : (bE₁ x t (E₁ y A)) = (E₁ y (bE₁ x t A)) := by sorry

lemma Prenex3 (x y : String) (q : Term) (A : Formula) : (E₁ x (bE₁ y q A)) = (bE₁ y q (E₁ x A)) := by sorry

lemma Prenex4 (x y : String) (t q : Term) (A : Formula) : (E₁ x (bE₁ y q A)) = (bE₁ y q (E₁ x A)) := by sorry

lemma Prenex5 (x y : String) (t q : Term) (A : Formula) : (bE₁ x t (bE₁ y q A)) = (bE₁ y q (bE₁ x t A)) := by sorry

-----------

lemma BiPrenex1 (x : String) (A B : Formula) (x ∈ A.freevars) (x ∈ B.freevars) :
    ((E₁ x A) ∨₁ (E₁ x B)) = (E₁ x (A ∨₁ B)) := by sorry

lemma BiPrenex2 (x : String) (t : Term) (A B : Formula) (x ∈ A.freevars) (x ∈ B.freevars) :
    ((E₁ x t A) ∨₁ (E₁ x t B)) = (E₁ x t (A ∨₁ B)) := by sorry

lemma BiPrenex3 (x : String) (A B : Formula) (x ∈ A.freevars) (x ∈ B.freevars) :
    ((E₁ x A) ∧₁ (E₁ x B)) = (E₁ x (A ∧₁ B)) := by sorry

lemma BiPrenex4 (x : String) (t : Term) (A B : Formula) (x ∈ A.freevars) (x ∈ B.freevars) :
    ((bE₁ x t A) ∧₁ (bE₁ x t B)) = (bE₁ x t (A ∧₁ B)) := by sorry

lemma BiPrenex5 (x : String) (A B : Formula) (x ∈ A.freevars) (x ∈ B.freevars) :
    ((V₁ x A) ∧₁ (V₁ x B)) = (V₁ x (A ∧₁ B)) := by sorry

lemma BiPrenex6 (x : String) (t : Term) (A B : Formula) (x ∈ A.freevars) (x ∈ B.freevars) :
    ((bV₁ x t A) ∧₁ (bV₁ x t B)) = (bV₁ x t (A ∧₁ B)) := by sorry

-----------

lemma ThricePrenex1 (x y : String) (A B : Formula)
    (x ∈ A.freevars) (x ∉ B.freevars)
    (x ∉ A.freevars) (x ∈ B.freevars):
    ((V₁ x A) ∧₁ (V₁ y B)) = (V₁ x (V₁ y (A ∧₁ B))) := by sorry

lemma ThricePrenex2 (x y : String) (t q : Term) (A B : Formula)
    (x ∈ A.freevars) (x ∉ B.freevars)
    (y ∉ A.freevars) (y ∈ B.freevars):
    ((bV₁ x t A) ∧₁ (bV₁ y q B)) = (bV₁ x t (bV₁ y q (A ∧₁ B))) := by sorry

----------

lemma HalfPrenex1 (x : String) (A B : Formula) (x ∈ A.freevars) (x ∉ B.freevars):                 -- TODO: versão com ∨₁ para def
    ((V₁ x A) ∧₁ B) = (V₁ x (A ∧₁ B)) := by sorry

lemma HalfPrenex1 (x : String) (t : Term) (A B : Formula) (x ∈ A.freevars) (x ∉ B.freevars):      -- TODO: versão com ∨₁ para def
    ((bV₁ x t A) ∧₁ B) = (bV₁ x t (A ∧₁ B)) := by sorry

lemma HalfPrenex3 (x : String) (A B : Formula) (x ∈ A.freevars) (x ∉ B.freevars):
    ((E₁ x A) ∧₁ B) = (E₁ x (A ∧₁ B)) := by sorry

lemma HalfPrenex4 (x : String) (t : Term) (A B : Formula) (x ∈ A.freevars) (x ∉ B.freevars):
    ((bE₁ x t A) ∧₁ B) = (bE₁ x t (A ∧₁ B)) := by sorry

lemma HalfPrenex5 (x : String) (A B : Formula) (x ∈ A.freevars) (x ∉ B.freevars):
    ((E₁ x A) ∨₁ B) = (E₁ x (A ∨₁ B)) := by sorry

lemma HalfPrenex6 (x : String) (t : Term) (A B : Formula) (x ∈ A.freevars) (x ∉ B.freevars):
    ((bE₁ x t A) ∨₁ B) = (bE₁ x t (A ∨₁ B)) := by sorry

TODO: what is missing?

-/



-- Problema
/- TODO (14 ag) : Prenexification rules as axioms (keeps def and prim symbols)? Or as lemmas (does not keep)?
axiom L_DM_or (A B : LFormula) : (¬₀(A∨₀B)) = ((¬₀A)∧₀(¬₀B))
lemma L_DM_or (A B : LFormula) : (¬₀(A∨₀B)) = ((¬₀A)∧₀(¬₀B)) := by sorry
-/

-- DeMorgan laws
axiom prenex_DM_or (A B : Formula) :
      (¬₁(A∨₁B)) = ((¬₁A)∧₁(¬₁B))
axiom prenex_DM_and (A B : Formula) :
      (¬₁(A∧₁B)) = ((¬₁A)∨₁(¬₁B))

-- Negation
axiom prenex_neg_exists (A : Formula) (x : String) :
      (¬₁(E₁ x A)) = (V₁ x (¬₁A))
axiom prenex_neg_forall (A : Formula) (x : String) :
      (¬₁(V₁ x A)) = (E₁ x (¬₁A))

-- Conjunction
axiom prenex_forall_and (A B : Formula) (x : String) (hA : x ∈ A.freevars) (hB : x ∉ B.freevars) :
      ((V₁ x A)∧₁B) = (V₁ x (A∧₁B))
axiom prenex_exists_and (A B : Formula) (x : String) (hA : x ∈ A.freevars) (hB : x ∉ B.freevars) :
      ((E₁ x A)∧₁B) = (E₁ x (A∧₁B))

-- "Forall unite" (conj and disj)
axiom prenex_forall_or_un (A B : Formula) (x : String) :
      ((V₁ x A)∨₁(V₁ x B)) = (V₁ x (A∨₁B))
axiom prenex_forall_and_un (A B : Formula) (x : String) :
      ((V₁ x A)∧₁(V₁ x B)) = (V₁ x (A∧₁B))

-- "Exists unite" (conj and disj)
axiom prenex_exists_or_un (A B : Formula) (x : String) :
      ((E₁ x A)∨₁(E₁ x B)) = (E₁ x (A∨₁B))
axiom prenex_exists_and_un (A B : Formula) (x : String) :
      ((E₁ x A)∧₁(E₁ x B)) = (E₁ x (A∧₁B))

-- "Forall commutativity" (unbounded and bounded)
axiom prenex_unbforall_comm (A B : Formula) (x y : String) :
      (V₁ x (V₁ y A)) = (V₁ y (V₁ x A))
axiom prenex_bforall_comm (A B : Formula) (x y : String) (t q : Term) :
      (bV₁ x t (bV₁ y q A)) = (bV₁ y q (bV₁ x t A))

-- "Exists commutativity" (unbounded and bounded)
axiom prenex_unbexists_comm (A B : Formula) (x y : String) :
      (E₁ x (E₁ y A)) = (E₁ y (E₁ x A))
axiom prenex_bexists_comm (A B : Formula) (x y : String) (t q : Term) :
      (bE₁ x t (bE₁ y q A)) = (bE₁ y q (bE₁ x t A))

-- "Exists and forall comm" (unbounded and bounded)

-- "Bounded and unbounded forall comm"
axiom prenex_b_unb_forall_comm (A B : Formula) (x y : String) (t : Term) :
      (bV₁ x t (V₁ y A)) = (V₁ y (bV₁ x t A))

-- "Bounded and unbounded exists comm"
axiom prenex_b_unb_exists_comm (A B : Formula) (x y : String) (t : Term) :
      (bE₁ x t (E₁ y A)) = (E₁ y (bE₁ x t A))


-- Disjunction
axiom prenex_forall_or (A B : Formula) (x : String) (hA : x ∈ A.freevars) (hB : x ∉ B.freevars) :
      ((V₁ x A)∨₁B) = (V₁ x (A∨₁B))
axiom prenex_exists_or (A B : Formula) (x : String) (hA : x ∈ A.freevars) (hB : x ∉ B.freevars) :
      ((E₁ x A)∨₁B) = (E₁ x (A∨₁B))

-- Implication
axiom prenex_forall_imp (A B : Formula) (x : String):
      ((V₁ x A)→₁B) = (E₁ x (A→₁B))     -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)
axiom prenex_exists_imp (A B : Formula) (x : String) :
      ((E₁ x A)→₁B) = (V₁ x (A→₁B))    -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)

axiom prenex_imp_forall (A B : Formula) (x : String):
      (A→₁(V₁ x B)) = (V₁ x (A→₁B))     -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)
axiom prenex_imp_exists (A B : Formula) (x : String) :
      (A→₁(V₁ x B)) = (E₁ x (A→₁B))    -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)




-- ------------------

-- Conjunction commutativity
axiom and_commut (A B : Formula) : (A∧₁B) = (B∧₁A)

-- Disjunction commutativity
axiom or_commut (A B : Formula) : (A∨₁B) = (B∨₁A)

-- ------------------

-- Double neg
axiom double_neg (A : Formula) : (¬₁(¬₁A)) = A


-- AGORA: 0. Which ones need the assumption of in and notin freevars?
--        1. acrescentar as assumptions que em StarLang devem funcionar
--        2. acabar as prenex rules aqui (falta os bounded chanesses pelo menos )









/-
t₁,...,tₙ
∃t∈lt

-/



end StarLang
