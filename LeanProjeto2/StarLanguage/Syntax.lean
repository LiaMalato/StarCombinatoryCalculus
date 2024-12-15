import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Batteries

open LFormula
open LTerm
open Batteries

-- -------------------------------------------------------------
-- -------------------------------------------------------------
--             STAR LANGUAGE - THE SYNTAX
--            (SECTION 1.2.1: The syntax)
-- -------------------------------------------------------------
-- -------------------------------------------------------------

/- FILE DESCRIPTION:
In this file we discuss the syntax.
The file corresponds to pages 8 to 13.
-/

-- -------------------------------------------------------------
--                     TERMS (p.10-12)
-- -------------------------------------------------------------

-- -------------------------------------------------------------
-- DEFINITIONS 1.2 AND 1.3 (p.9-10):
-- Constants and terms of L^ω_*
-- -------------------------------------------------------------

-- DEFINITION: Terms of L^ω_*
inductive Term
| lcons : String → Term                 -- L-constants: constants from L
| lfun : String → Term                  --              function symbols of L
| pi                                    -- combinators:     Π
| sigma                                 --                  Σ
| sing                                  -- star constants:  𝔰
| bUnion                                --                  ∪ (binary union)
| iUnion                                --                  ∪ (indexed union)
| var : String → Term                   -- variables
| app : Term → Term → Term              -- application of terms
deriving Repr, DecidableEq

open Term

-- NOTATION: Notation for combinators and star constants
notation "Π₁" => pi
notation "Σ₁" => sigma
notation "𝔰₁" => sing
notation "∪₁" => bUnion
notation "i∪₁" => iUnion

-- NOTATION: Notation for the application of terms
notation t₁ "·" t₂ => app t₁ t₂

-- EXAMPLE: some terms (variables) to use in future examples
--namespace examples
def var_x := var "x"
def var_y := var "y"
def var_z := var "z"
-- end examples


-- --------------------------------
-- TUPLES OF TERMS
-- --------------------------------

-- Term tuples will be defined as lists of terms.
-- For example, if t₁ t₂ : Term, then [t₁, t₂] : List Term.

-- DEFINITION: We define a function in order to access any element in a tuple.
-- The use of Option allows to get some/none. This is useful for instance if a term tuple
-- has 2 elements and we ask for the (non-existing) third element. The output is then 'none'.
def getElement (n : Nat) (t : List Term) : Option Term :=
  List.get? t n

-- -------
-- EXAMPLES: a tuple of terms and accessing its elements
-- -------

--namespace examples
def exTermTuple : List Term := [var_x, var_y]  -- a tuple of terms (a list with the variables x and y)

#eval getElement 0 exTermTuple          -- Output: var_x (the first element of exTermTuple)
#eval getElement 1 exTermTuple          -- Output: var_y (the second element of exTermTuple)
#eval getElement 2 exTermTuple          -- Output: none (there is no third element in exTermTuple)
--end examples

-- ------------------------
-- NOTATION 1.4 (p. 12):
-- Term tuple applications
-- ------------------------

-- DEFINITION: Term tuple applications
@[simp]
def TermTupleApp : List Term → List Term → List Term
| [], _   => []         -- If the first tuple is empty, return an empty list
| _ , []  => []         -- If the second tuple is empty, return an empty list
| (t :: ts), qs =>      -- Nests the applications of terms as in the mathematical definition
  let appNested := qs.reverse.foldr (fun q acc => app acc q) t
  (appNested :: (TermTupleApp ts qs))

-- NOTATION: term tuple applications will be written using ⊙
@[simp]
notation t₁ "⊙" t₂ => TermTupleApp t₁ t₂

-- --------------
-- TECHNICALITIES:
-- Auxilliary lemmas related to term tuple applications with empty tuples
-- --------------

@[simp]
lemma app_empty_list_fst (t : List Term) : (TermTupleApp [] t) = [] :=
by
  rw [TermTupleApp]

@[simp]
lemma app_empty_list_sec (t : List Term) : (TermTupleApp t []) = [] :=
by
  induction t
  case nil =>
    rw [TermTupleApp]
  case cons _ _ _ =>
    simp

@[simp]
lemma app_empty_lists : (TermTupleApp [] []) = [] :=
by
  rw [TermTupleApp]

-- --------
-- EXAMPLES: Applications between term tuples
-- --------

-- namespace examples
-- The tuple consisting of the variable 'x' is a term tuple
#check [var_x]
#eval [var_x]

-- Applying two empty tuples yields the empty tuple
#eval TermTupleApp ([] : List Term) ([] : List Term)

-- Term tuple applications
def ex_app1 : List Term := [var "t1", var "t2"] ⊙ [var "q1", var "q2", var "q3"]
#eval ex_app1       -- Output: t₁q₁q₂q₃, t₂q₁q₂q₃

def ex_app2 : List Term := [var "t1", var "t2", var "t3"] ⊙ [var "q1", var "q2", var "q3"]
#eval ex_app2       -- Output: t₁q₁q₂q₃, t₂q₁q₂q₃, t₃q₁q₂q₃

def ex_app3 : List Term := [var "t1", var "t2"] ⊙ [var "q1", var "q2", var "q3", var "q4"]
#eval ex_app3       -- Output: t₁q₁q₂q₃q₄, t₂q₁q₂q₃q₄
-- end examples


-- -------------------------------
-- TECHNICALITIES in order to use TermTupleApp directly with strings instead of terms
-- Functions to transform lists of one type into lists of other types.
-- -------------------------------

-- DEFINITION: Function to transform a list of Strings into a list of 'Term.var',
-- i.e. turning 'ts : List String' into 't : List Term', but more specifically each term in t has type 'Term.var'
@[simp]
def List.tt (lst : List String) : List Term :=
  lst.map Term.var

-- --------
-- EXAMPLE:
-- --------

-- namespace examples
#check "w"            -- Output: String
#check ["w"]          -- Output: List String
#check ["w"].tt       -- Output: List Term
#eval ["w"].tt        -- Output: "w" is a variable

#eval (["w"].tt)⊙(["w"].tt)     -- Output: term application 'w·w'
-- end examples


-- --------------------------------
-- WELL-FORMED TERMS
-- --------------------------------

-- DEFINITION: well-formed terms
inductive Term_is_wellformed : List String → Term → Prop
| wf_lcons {xs k} : x ∈ xs → Term_is_wellformed xs (lcons k)
| wf_lfun {xs f} : x ∈ xs → Term_is_wellformed xs (lfun f)
| wf_pi {xs} : Term_is_wellformed xs pi
| wf_sigma {xs} : Term_is_wellformed xs sigma
| wf_sing {xs} : Term_is_wellformed xs sing
| wf_bUnion {xs} : Term_is_wellformed xs bUnion
| wf_iUnion {xs} : Term_is_wellformed xs iUnion
| wf_var {xs x} : x ∈ xs → Term_is_wellformed xs (var x)
| wf_app {xs t1 t2} : Term_is_wellformed xs t1 → Term_is_wellformed xs t2 → Term_is_wellformed xs (app t1 t2)

-- DEFINITION: well-formed tuple of terms
-- If each term in the tuple is well-formed so is the whole tuple
inductive TermTuple_is_wellformed : List String → List Term → Prop
| wf_tuple : (∀ t ∈ ts, Term_is_wellformed xs t) → (TermTuple_is_wellformed xs ts)


-- --------------------------------
-- SUBTERMS
-- --------------------------------

namespace Term

-- DEFINITION: subterm of a term
inductive isSubterm : Term → Term → Prop
| refl (t : Term) :             isSubterm t t                                       -- Terms are always subterms of themselves
| app_left {t₁ t₂ t' : Term} :  isSubterm t' t₁ → isSubterm t' (Term.app t₁ t₂)     -- Subterms of applications (LHS)
| app_right {t₁ t₂ t' : Term} : isSubterm t' t₂ → isSubterm t' (Term.app t₁ t₂)     -- Subterms of applications (RHS)

open isSubterm

-- DEFINITION: subterms of tuple of terms
inductive isSubtermTuple : List Term → List Term → Prop
| empty_subtuple : isSubtermTuple [] []                           -- The empty tuple is a subtuple of itself
| rec_subtuple {t₁ t₂ : Term} {ts₁ ts₂ : List Term} :             -- Recursive definition for non-empty tuples
    isSubterm t₁ t₂ →
    isSubtermTuple ts₁ ts₂ →
    isSubtermTuple (t₁ :: ts₁) (t₂ :: ts₂)

-- -------
-- EXAMPLE: checking if the variable 'x' is a subterm of the term application x·y
-- -------

example : isSubterm (var "x") (app (var "x") (var "y")) :=
  by
    have H := isSubterm.refl (var "x")
    exact app_left H


-- -------------------------------------
-- FREE VARIABLES FOR TERMS
-- -------------------------------------

-- DEFINITION: all the (free) variables of terms, it returns the set of (free) variables
def freevars : Term → Finset String
| (lcons k)
| (lfun f)
| pi
| sigma
| sing
| bUnion
| iUnion => {}
| var x => {x}
| app t₁ t₂ => t₁.freevars ∪ t₂.freevars

-- DEFINITION: (free) variables in tuples of terms
def freevarsTuple (tuple : List Term) : Finset String :=
  (tuple.map freevars).foldl (fun acc fv => acc ∪ fv) ∅


-- ---------------------------------------
-- CLOSED TERMS
-- ---------------------------------------

-- DEFINITION: closed terms and closed tuple terms
def isClosedTerm (t : Term) : Prop := freevars t = {}
def isClosedTupleTerm (t : List Term) : Prop := freevarsTuple t = {}


-- ------------------------------------------------------
-- TYPECHECKING THE TERMS OF L^{omega}_*
-- ------------------------------------------------------

/- DEFINITION: Term_TypeChecking a term
We typecheck the components of the formulas of L^ω_*. This guarantees that the formulas have admissible types.
-/

def arities {n : Nat} : String → Option Nat
| "f" => .some n
| _ => .none

def type_from_arity : Nat → FType
| 0 => G
| (n + 1) => G ⟶ (type_from_arity n)

inductive Term_TypeChecking : Term → FType → Prop
| tcLcons {k}:          Term_TypeChecking (lcons k)  G
| tcLfun {f} {n}:       arities f = (.some n)  → Term_TypeChecking (lfun f) (type_from_arity n)
| tcPi {σ τ}:           Term_TypeChecking pi        (σ ⟶ (τ ⟶ σ))                                 -- Π_{σ,τ} : σ ⟶ (τ ⟶ σ)
| tcSigma {σ τ ρ}:      Term_TypeChecking sigma     ((σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ)))      -- Σ_{σ,τ,ρ} : (σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ))
| tcSing {σ}:           Term_TypeChecking sing      (σ ⟶ σ⋆)                                       -- 𝔰_{σ} : σ⋆
| tcBUnion {σ}:         Term_TypeChecking bUnion    (σ⋆ ⟶ (σ⋆ ⟶ σ⋆))                              -- ∪_{σ} : σ⋆ ⟶ (σ⋆ ⟶ σ⋆)
| tcIUnion {σ τ}:       Term_TypeChecking iUnion    (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆))                       -- i∪_{σ} : σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆)
| tcVar {x σ}:          Term_TypeChecking (var x)   σ                                              -- Variables x : σ
| tcApp {t₁ t₂ σ τ}:    Term_TypeChecking t₁ (σ ⟶ τ) →
                        Term_TypeChecking t₂ σ →
                        Term_TypeChecking (app t₁ t₂) τ                                            -- If t₁ : (σ ⟶ τ) and t₂ : σ, then t₁t₂ : τ

-- DEFINITION: Term_TypeChecking for tuples of terms
inductive TermTuple_TypeChecking : List Term → List FType → Prop
| tcRecTuple {t : Term} {σ : FType} {ts : List Term} {σs : List FType} :
    Term_TypeChecking t σ →                             -- If the first term has the first type of the list of types
    TermTuple_TypeChecking ts σs →                      -- if the other terms in the tuple have the corresponding types in the list of types
    TermTuple_TypeChecking (t :: ts) (σ :: σs)          -- then the whole tuple typechecks.

open Term_TypeChecking


-- -------------------------------------
-- TERM SUBSTITUTION IN L^ω_*
-- -------------------------------------

-- DEFINITION: term substitution, we replace 'x' by 'replacement' in some term 't' (lcons, var, app, rest)
def term_substitution (x : String) (replacement : Term) : Term → Term
| lcons k   => lcons k
| lfun f    => lfun f
| var y     => if x = y
               then replacement
               else (var y)
| app t₁ t₂ => app (term_substitution x replacement t₁) (term_substitution x replacement t₂)  -- In an application, we do the substitution in each term
| t => t                                                                                      -- The combinators Π, Σ and the star constants 𝔰, ∪, ⋃ are constants and hence are not affected by substitution

-- DEFINITION: term substitution for term tuples, we substitute 'x' by 'replacement' in some term tuple 't'
def term_substitutionTuple (x : String) (replacement : Term) : List Term → List Term
| [] => []
| (t :: ts) => (term_substitution x replacement t) :: term_substitutionTuple x replacement ts

-- ---------
-- EXAMPLES: substitutions
-- ---------

-- EXAMPLE: term substitution
#eval term_substitution "x" Π₁ (var_x)                                -- Replacing x by Π₁ in x gives Π₁
#eval term_substitution "x" Π₁ (var_y)                                -- Replacing x by Π₁ in y gives y
#eval term_substitution "x" ∪₁ (((var_x)·(var_y))·(var_z))            -- Replacing x by ∪₁ in (x·y)·z gives (∪₁·y)·z

-- EXAMPLE: term tuple substitution
-- We substitute "x" by an lconstant a in the tuple [x, (y·z)]
#eval term_substitutionTuple "x" (lcons "c") [var_x, (Π₁·var_y)]       -- Output: [c, (Π₁·z)]

end Term


-- -------------------------------------------------------------
--                     FORMULAS (p.12-14)
-- -------------------------------------------------------------

/-
We define the formulas of L^ω_*:
  a) The atomic formulas (Definition 1.6 - p.11)
  b) The base formulas (Definition 1.10 - p.14)
  c) The formulas (Definition 1.7 - p.13)
-/

-- -------------------------------------------------------------
-- DEFINITION 1.7 (p.13):
-- Formulas of L^ω_*
-- -------------------------------------------------------------

inductive Formula : Type
| rel:         String → List Term → Formula             -- R(t₁, ..., tₙ) with R relational symbol of L and t₁,...,tₙ ground terms in L^ω_*
| eq:          Term → Term → Formula                    -- t =σ q
| mem:         Term → Term → Formula                    -- t ∈σ q
| not:         Formula → Formula                        -- If A is a formula, then so is (¬A)
| or:          Formula → Formula → Formula              -- If A and B are formulas, then so is (A∨B)
| unbForall:   String → Formula → Formula               -- If A is a formula, then so is (∀x A)
| bForall:     String → Term → Formula → Formula        -- If A is a formula, then so is (∀x∈t A)
deriving Repr

open Formula


-- ------------------------------------
-- UNIVERSAL QUANTIFICATIONS FOR TUPLES
-- ------------------------------------

-- DEFINITION: ∀ (unbounded) for tuples
-- We convert the list of variables into a nested sequence of ∀ quantifiers
def unbForallTuple (vars : List String) (A : Formula) : Formula :=
  vars.foldr (fun v acc => Formula.unbForall v acc) A

-- DEFINITION: ∀ (bounded) for tuples
def bForallTuple (vars : List String) (terms : List Term) (A : Formula) : Formula :=
  let applyBForall := List.zip vars terms                             -- Applies bForall using the variable and corresponding term.
  applyBForall.foldr (fun (v, t) acc => Formula.bForall v t acc) A    -- Folds over the list of (variable, term) pairs.
                                                                      -- This is done by applying bForall and this in the correct order.

-- TECHNICAL DEFINITION:
-- If the lists are empty, then folding over them, gives just the initial formula 'A'.
@[simp]
theorem bForallTuple_nil (A : Formula) :
  bForallTuple [] ([].tt) A = A :=
by
  unfold bForallTuple
  simp

open Formula


-- ---------------------------
-- NOTATION: Primitive symbols
-- ---------------------------

-- Here we introduce notation to get closer to the mathematical definition.
-- To avoid clashes with the core notations already present in Lean, we add '₁' to each symbol in L^ω_*.

-- NOTATION: Notation for the equality and the membership symbols
notation t₁ "=₁" t₂ => Formula.eq t₁ t₂
notation t₁ "∈₁" t₂ => Formula.mem t₁ t₂

-- NOTATION: Notation for the primitive symbols ¬, ∨, ∀x and ∀x∈t in L^ω_*
notation "¬₁" A   => not A
notation A "∨₁" B => or A B
notation "∀₁₁"    => unbForall
notation "b∀₁₁"   => bForall
notation "∀₁"     => unbForallTuple   -- unbounded universal quantifier for tuples
notation "b∀₁"    => bForallTuple     -- bounded universal quantifier for tuples


-- -----------------------------------------------------------------------
-- DEFINITION 1.8 (p.14):
-- The bounded and unbounded existential quantifiers ∃x∈t (defined symbol)
-- -----------------------------------------------------------------------

-- DEFINITION: The unbounded existential quantifier (single variable):          ∃x A := ¬ (∀x (¬ A))
@[simp]
def unbExists (x : String) (A : Formula) : Formula :=
  ¬₁(∀₁₁ x (¬₁ A))

-- DEFINITION: The bounded existential quantifier (single):                     ∃x∈t A := ¬ (∀x∈t (¬ A))
@[simp]
def bExists (x : String) (t : Term) (A : Formula) : Formula :=
  ¬₁(b∀₁₁ x t (¬₁ A))

-- DEFINITION: The unbounded existential quantifier (for tuples of variables):  ∃x A := ¬ (∀x (¬ A))
@[simp]
def unbExistsTuple (x : List String) (A : Formula) : Formula :=
  ¬₁ (∀₁ x (¬₁A))

-- DEFINITION: The bounded existential quantifier (for tuples):                 ∃x∈t A := ¬ (∀x∈t (¬ A))
@[simp]
def bExistsTuple (x : List String) (t : List Term) (A : Formula) : Formula :=
  ¬₁ (b∀₁ x t (¬₁A))

-- NOTATION: bounded and unbounded existential quantifiers
notation "∃₁₁" => unbExists
notation "b∃₁₁" => bExists
notation "∃₁" => unbExistsTuple
notation "b∃₁" => bExistsTuple


-- --------------------------------------------------------------------
-- DEFINITION and NOTATION: the rest of the defined symbols (p.9):
-- Usual logical abbreviations for the defined symbols ∧, →, ↔ in L^ω_*
-- --------------------------------------------------------------------

-- DEFINITION: Conjunction:  A ∧ B := ¬(¬A∨¬B)
@[simp]
def F_and (A B : Formula) : Formula :=
  ¬₁ ((¬₁ A) ∨₁ (¬₁ B))

notation A "∧₁" B => F_and A B

-- DEFINITION: Implication:  A → B := ¬ A ∨ B
@[simp]
def F_implies (A B : Formula) : Formula :=
  (¬₁ A) ∨₁ B

notation A "→₁" B => F_implies A B

-- DEFINITION: Equivalence:  A ↔ B := (A → B) ∧ (B → A)
@[simp]
def F_iff (A B : Formula) : Formula :=
  ¬₁ ((¬₁((¬₁A) ∨₁ B)) ∨₁ (¬₁((¬₁B) ∨₁ A)))
  -- (A →₁ B) ∧₁ (B →₁ A)
  -- (¬₁ A ∨₁ B) ∧₁ (¬₁ B ∨₁ A)

notation A "↔₁" B => F_iff A B


-- ------------------------------------------------------
-- DEFINITION: Membership and equality symbols for tuples
-- ------------------------------------------------------

-- DEFINITION: Membership symbol (tuples):
-- Function that takes two lists of terms and applies 'mem', ∈, pairwise to corresponding elements of the lists.
def mem_tuple : List Term → List Term → Formula
| [], [] => Formula.rel "True" []                         -- When the lists are empty
| (t1::ts), (q1::qs) => (t1 ∈₁ q1) ∧₁ (mem_tuple ts qs)   -- Recursively creates pairwise ∈
| _, _ => Formula.rel "False" []                          -- Other cases (for example, when the lists have different lengths)

notation lt₁ "∈_t" lt₂ => mem_tuple lt₁ lt₂

-- DEFINITION: Equality symbol (tuples):
-- Function that takes two lists of terms and applies 'eq', =, pairwise to corresponding elements of the lists.
def eq_tuple : List Term → List Term → Formula
| [], [] => Formula.rel "True" []                         -- When the lists are empty
| (t1::ts), (q1::qs) => (t1 =₁ q1) ∧₁ (eq_tuple ts qs)    -- Recursively creates pairwise =
| _, _ => Formula.rel "False" []                          -- Other cases (for example, when the lists have different lengths)

notation lt₁ "=_t" lt₂ => eq_tuple lt₁ lt₂


-- -----------------------------
-- WELL-FORMED FORMULAS IN L^ω_*
-- -----------------------------

inductive Formula_is_wellformed : List String → Formula → Prop
| wf_rel {xs R ts} :
    (∀ t ∈ ts, Term_is_wellformed xs t) →
    Formula_is_wellformed xs (rel R ts)           -- If t₁,...,tₙ are well-formed terms, then so is R(t₁,...,tₙ).
| wf_eq {xs t₁ t₂} :
    Term_is_wellformed xs t₁ →
    Term_is_wellformed xs t₂ →
    Formula_is_wellformed xs (eq t₁ t₂)           -- If t₁ and t₂ are well-formed, then so is t₁=t₂.
| wf_mem {xs t₁ t₂} :
    Term_is_wellformed xs t₁ →
    Term_is_wellformed xs t₂ →
    Formula_is_wellformed xs (mem t₁ t₂)          -- If t₁ and t₂ are well-formed, then so is t₁∈t₂.
| wf_not {xs A} :
    Formula_is_wellformed xs A →
    Formula_is_wellformed xs (not A)              -- If A is a well-formed formula, then so is ¬A.
| wf_or {xs A B} :
    Formula_is_wellformed xs A →
    Formula_is_wellformed xs B →
    Formula_is_wellformed xs (or A B)             -- If A and B are well-formed formulas, then so is A∨B.
| wf_unbForall {xs x A} :
    Formula_is_wellformed (x :: xs) A →
    Formula_is_wellformed xs (unbForall x A)      -- If A is a well-formed formula (for our list xs and the bound variable x), then so is ∀x A.
| wf_bForall {xs x t A} :
    Formula_is_wellformed (x :: xs) A →
    Formula_is_wellformed xs (bForall x t A)      -- Analogously for ∀x∈t A


-- -------------------------------------
-- FREE VARIABLES FOR FORMULAS IN L^ω_*
-- -------------------------------------

-- DEFINITION: the free variables of a formula
def Formula.freevars : Formula → Finset String
| .rel _ ts       => Finset.fold (fun x y => x ∪ y) {} Term.freevars ts.toFinset
| .eq t₁ t₂
| .mem t₁ t₂      => t₁.freevars ∪ t₂.freevars
| .or A B         => A.freevars ∪ B.freevars
| .not A          => A.freevars
| .unbForall x A
| .bForall x t A  => A.freevars \ ([x].toFinset)

-- DEFINITION: all the variables of a formula
def Formula.allvars : Formula → Finset String
| .rel _ ts       => Finset.fold (fun x y => x ∪ y) {} Term.freevars ts.toFinset    -- All the variables from the list of terms used in the predicate.
| .eq t₁ t₂
| .mem t₁ t₂      => t₁.freevars ∪ t₂.freevars                                      -- For both terms, we collect the variables from both and consider the union of those sets.
| .or A B         => A.allvars ∪ B.allvars                                          -- Take the variables from both subformulas and consider the union of those sets.
| .not A          => A.allvars                                                      -- The variables of ¬A are the ones of A.
| .unbForall x A  => A.allvars ∪ {x}                                                -- The variables of ∀x A are the ones of A together with the bound variable.
| .bForall x t A  => t.freevars ∪ A.allvars ∪ {x}                                   -- The variables of ∀x∈t A are the ones of A together with the bound variable and the variables in t.

/-
With these definitions, we can create assumptions such as:
    x is a free variable of formula A       -> In Lean: x ∈ A.freevars
    x is not a free variable of formula A   -> In Lean: x ∉ A.freevars

    x is a variable of formula A            -> In Lean: x ∈ A.allvars
    x is not a variable of formula A        -> In Lean: x ∉ A.allvars
-/


-- ----------------------------
-- SENTENCES (CLOSED FORMULAS)
-- ----------------------------

def isClosed (A : Formula) : Prop := Formula.freevars A = {}
def isClosed_check (A : Formula) : Bool := (Formula.freevars A) = {}       -- Prints true or false depending on if there are free variables or not

-- ---------
-- EXAMPLES: Free variables and checks whether it is a sentence
-- ---------

-- EXAMPLE 1: Formula R(x,y) ∨ (∀z Q(z))
def ex1_freevars_formula := (rel "R" [var "x", var "y"]) ∨₁ (∀₁₁ "z" (rel "Q" [var "z"]))
#eval Formula.freevars ex1_freevars_formula                         -- The set of free variables is the set {x,y}, that is {"x", "y"}.
#eval isClosed_check ex1_freevars_formula                           -- Since ex1_freevars_formula has x and y as free variables, the output is false.

-- EXAMPLE 2: Formula R(x,y)
def ex2_freevars_formula := (rel "R" [var "x", var "y"])
#eval Formula.freevars ex2_freevars_formula                         -- The set of free variables is the set {x,y}, that is {"x", "y"}.
#eval isClosed_check ex2_freevars_formula                           -- Since ex2_freevars_formula has x and y as free variables, the output is false.

-- EXAMPLE 3: Formula R(x,y)
def ex3_freevars_formula := (∀₁₁ "x" (rel "R" [var "x"]))
#eval Formula.freevars ex3_freevars_formula                         -- There are no free variables, the set of free variables is ∅.
#eval isClosed_check ex3_freevars_formula                           -- Since ex3_freevars_formula has no free variables, the output is true.


-- ------------------------------------------------------
-- ATOMIC AND BASE FORMULAS
-- ------------------------------------------------------

-- DEFINITION: Outputs a proposition stating that a formula is atomic:
inductive isAtomic : Formula → Prop
| at_rel (R : String) (l_term : List Term): isAtomic (rel R l_term)             -- Formulas of the form R(t₁,...,tn) are atomic
| at_eq (t₁ t₂ : Term) : isAtomic (eq t₁ t₂)                                    -- Formulas of the form t₁∈t₂ are atomic
| at_mem (t₁ t₂ : Term) : isAtomic (mem t₁ t₂)                                  -- Formulas of the form t₁=t₂ are atomic

-- DEFINITION: Outputs a proposition stating that a formula is base:
inductive isBase : Formula → Prop
| b_atom : isAtomic A → isBase A                                                -- Atomic formulas are base formulas
| b_not (h: isBase A) : isBase (not A)                                          -- If A is base, then so is ¬₁A
| b_or (h1: isBase A) (h2 : isBase B) : isBase (or A B)                         -- If A and B are base, then so is A∨₁B
| b_bForall (x : String) (t : Term) (h : isBase A) : isBase (bForall x t A)     -- If A is base, then so is ∀x∈t A

open isAtomic
open isBase

-- ---------
-- EXAMPLES:
-- ---------

-- EXAMPLE 1: The formula p=q is atomic
example (p q : Term) : isAtomic (p =₁ q) := by
  exact at_eq p q

-- EXAMPLE 2: Let A be an atomic formula (assumption h), then it is base.
example (A : Formula) (h : isAtomic A)  : (isBase A) := by
  exact b_atom h

-- EXAMPLE 3: If A is an atomic formula and B is a base formula, then A∨B is base.
example (A B : Formula) (hA_at : isAtomic A) (hB_b : isBase B) : (isBase (A∨₁B)) := by
  have h := b_atom hA_at
  exact b_or h hB_b

-- EXAMPLE 4: The formula x=y is a base formula.
example (x y : String) : isBase ((var x) =₁ (var y)) := by exact b_atom (isAtomic.at_eq (var x) (var y))

-- ---------------------------------------------------------


-- -----------------------------------------------------------------------
-- REMARK 1.10 (p.14):
-- Defined symbols of base formulas are also base
-- -----------------------------------------------------------------------

-- LEMMA: Conj_base states that if A and B are base formulas, then so is their conjunction A ∧ B
lemma Conj_base (A B : Formula) (hA : isBase A) (hB : isBase B) : (isBase (A∧₁B)) := by
  unfold F_and
  exact b_not (b_or (b_not hA) (b_not hB))

-- LEMMA: Imp_base states that if A and B are base formulas, then so is their implication A → B
lemma Imp_base (A B : Formula) (hA : isBase A) (hB : isBase B) : (isBase (A→₁B)) := by
  unfold F_implies
  have h_nA := b_not hA
  exact b_or h_nA hB

-- LEMMA: Iff_base states that if A and B are base formulas, then so is their equivalence A ↔ B
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

-- LEMMA: unbForall_base states that if A is a base formula, then so is ∃x∈t A
lemma bExists_base {A : Formula} (x : String) (t : Term) (hA : isBase A) : (isBase (b∃₁₁ x t A)) := by
  unfold bExists
  have h_nA := b_not hA
  have h_unbForall_nA := b_bForall x t h_nA
  exact b_not h_unbForall_nA


-- ------------------
-- EXAMPLE 1.6 (p.14)
-- ------------------

-- EXAMPLE 1.6.1 (p.14): If B is a base formula, then so is ∀x∈t B(x)
example (B : Formula) (hB_b : isBase B) (x : String) (t : Term): (isBase (b∀₁₁ x t (¬₁ B))) := by
  have H := b_not hB_b
  exact b_bForall x t H

-- EXAMPLE 1.6.2 (p.14): If A and B are base formulas, then so is ∀x∈t ∃y∈q (A∨B)
example (A B : Formula) (hA_b : isBase A) (hB_b : isBase B) (x y : String) (t q : Term): (isBase (b∀₁₁ x t (b∃₁₁ y q (A ∨₁ B)))) := by
  have H_or_AB := b_or hA_b hB_b
  have H_bExists := bExists_base y q H_or_AB
  exact b_bForall x t H_bExists


-- -------------------------------------
-- FORMULA SUBSTITUTION IN L^ω_*
-- -------------------------------------

mutual
  def List.subst (ts : List Term) (substitutions : HashMap String Term) : List Term :=
  ts.map (fun t => Term.subst t substitutions)

  def Term.subst (t:Term) (substitutions:HashMap String Term) : Term :=
  match t with
  | lcons k => substitutions.findD k (lcons k)
  | lfun f => substitutions.findD f (lfun f)
  | pi => pi
  | sigma => sigma
  | sing => sing
  | bUnion => bUnion
  | iUnion => iUnion
  | var n => substitutions.findD n (var n)
  | app t₁ t₂ => app (t₁.subst substitutions) (t₂.subst substitutions)
end

def Formula.subst (A:Formula) (substitutions : HashMap String Term) : Formula :=
match A with
| rel s ts => rel s (ts.map (fun t => Term.subst t substitutions))    -- for lists of terms, this is enough
| eq t1 t2 => eq (t1.subst substitutions) (t2.subst substitutions)
| mem t1 t2 => mem (t1.subst substitutions) (t2.subst substitutions)
| not A' => not (A'.subst substitutions)
| or A1 A2 => or (A1.subst substitutions) (A2.subst substitutions)
| unbForall s A' => match substitutions.find? s with
                    | .none => unbForall s (A'.subst substitutions)
                    | .some _ => unbForall s A'
| bForall s t A' => match substitutions.find? s with
                    | .none => bForall s (t.subst substitutions) (A'.subst substitutions)
                    | .some _ => bForall s (t.subst substitutions) A'

def Formula.term_subst (A:Formula) (tr1 tr2:Term) : Formula :=
match A with
| rel s ts => rel s (ts.map (fun t => if t = tr1 then tr2 else t))    -- for lists of terms, this is enough
| eq t1 t2 => eq (if t1 = tr1 then tr2 else t1) (if t2 = tr1 then tr2 else t2)
| mem t1 t2 => mem (if t1 = tr1 then tr2 else t1) (if t2 = tr1 then tr2 else t2)
| not A' => not (A'.term_subst tr1 tr2)
| or A1 A2 => or (A1.term_subst tr1 tr2) (A2.term_subst tr1 tr2)
| unbForall s A' => unbForall s (A'.term_subst tr1 tr2)
| bForall s t A' => bForall s (if t = tr1 then tr2 else t) (A'.term_subst tr1 tr2)

-- -------------------------------------
-- FORMULA SUBSTITUTION IN L^ω_*
-- -------------------------------------

def substitution_formula (x : String) (replacement : Term) : Formula → Formula
-- | (L_Form A) => match replacement with
--               | .lcons r => L_Form (Lsubstitution_formula x r A)
--               | _ => (L_Form A)
| (rel R terms) => rel R (terms.map (term_substitution x replacement))
| (t₁ =₁ t₂) => (term_substitution x replacement t₁) =₁ (term_substitution x replacement t₂)
| (t₁ ∈₁ t₂) => (term_substitution x replacement t₁) ∈₁ (term_substitution x replacement t₂)
| (Formula.not A) => ¬₁ (substitution_formula x replacement A)                                                       -- recursivamente em A
| (Formula.or A B) => (substitution_formula x replacement A) ∨₁ (substitution_formula x replacement B)               -- recursivamente em A e B
| (∀₁₁ y A) => if x = y then ∀₁₁ y A
              else ∀₁₁ y (substitution_formula x replacement A)
| (b∀₁₁ y t A) => if x = y then b∀₁₁ y t A
              else (b∀₁₁ y t (substitution_formula x replacement A))

-- ---------
-- EXAMPLES: formula substitution
-- ---------

-- EXAMPLE 1: substituting x by Π in R(x,y)
#eval substitution_formula "x" Π₁ (rel "R" [var_x, var_y])        -- Output: R(Π₁,y)

-- EXAMPLE 2: substituting z by ∪ in (¬(x∈y))∨(z=w)
def ex2_subst : Formula :=
    (¬₁( (var "x")∈₁(var "y") )) ∨₁ ((var "z")=₁(var "w"))
#eval substitution_formula "z" ∪₁ ex2_subst                       -- Output: (¬₁(x ∈₁ y)) ∨₁ (∪₁ =₁ w)


-- ------------------------------------------------------
-- TYPECHECKING
-- We typecheck the components of the formulas of L^ω_*.
-- This guarantees that the formulas have admissible types.
-- ------------------------------------------------------

inductive Formula_TypeChecking : Formula → Prop
| tcRel {R l_terms} :                                               -- If R is a relational symbol,
    (∀ t, t ∈ l_terms → Term_TypeChecking t G) →                    -- if we apply R to a list l_terms of ground terms,
    Formula_TypeChecking (Formula.rel R l_terms)                    -- then R(t₁,...,tₙ) typechecks.
| tcEq {σ t₁ t₂} :
    Term_TypeChecking t₁ σ →
    Term_TypeChecking t₂ σ →
    Formula_TypeChecking (Formula.eq t₁ t₂)                         -- If t₁ and t₂ have the same type, then the formula t₁=t₂ type checks.
| tcMem {σ t₁ t₂} :
    Term_TypeChecking t₁ σ →                                        -- If t₁:σ
    Term_TypeChecking t₂ (σ⋆) →                                     -- and if t₂:σ*,
    Formula_TypeChecking (Formula.mem t₁ t₂)                        -- then the formula t₁∈t₂ type checks.
| tcNot {A} :
    Formula_TypeChecking A → Formula_TypeChecking (Formula.not A)   -- If formula A type checks, then so does ¬A.
| tcOr {A B} :
    Formula_TypeChecking A →
    Formula_TypeChecking B →
    Formula_TypeChecking (Formula.or A B)                           -- If formulas A and B type check, then so does A∨B.
| tcbForall {x σ t A} :
    Term_TypeChecking (Term.var x) σ →                              -- If x:σ,
    Term_TypeChecking t (σ⋆) →                                      -- if t:σ*
    Formula_TypeChecking A →                                        -- and if the formula A type checks,
    Formula_TypeChecking (Formula.bForall x t A)                    -- then so does ∀x∈t A.
| tcunbForall {x σ A} :
    Term_TypeChecking (Term.var x) σ →                              -- If x:σ
    Formula_TypeChecking A →                                        -- and if the formula A type checks,
    Formula_TypeChecking (Formula.unbForall x A)                    -- then so does ∀x A.
