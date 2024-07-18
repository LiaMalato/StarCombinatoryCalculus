-- -------------------------------------------------------------
--            Star Language (atualizada)
-- -------------------------------------------------------------

-- We import the definitions from the first-order language L:
import LeanProjeto2.FOL
import MathLib.Tactic

open FOL

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
| pi                                    -- combinators:     Π
| sigma                                 --                  Σ
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
| wf_lcons {xs} {t : LTerm} : LTerm_is_wellformed_inStar xs t → Term_is_wellformed xs (lcons t)           -- TODO: não sei porque com LTerm.LTerm_is_wellformed não funciona tbm
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

inductive closed_under : Term → Finset String → Prop
| cu_lcons : closed_under (.lcons xs) α
| cu_pi : closed_under (.pi) α
| cu_sigma : closed_under (.sigma) α
| cu_sing : closed_under (.sing) α
| cu_bUnion : closed_under (.bUnion) α
| cu_iUnion : closed_under (.iUnion) α
| cu_var :
    x ∈ α →
    -----------
    closed_under (.var x) α
| cu_app : closed_under (app t₁ t₂) α               -- is this even right?

-- -------------------------------------
-- FREE VARIABLES PARA TERMOS EM L^ω_*
-- -------------------------------------

def freevars : Term → Finset String
| .lcons x => x.Lfreevars
| .pi
| .sigma
| .sing
| .bUnion
| .iUnion => {}
| .var x => {x}
| .app x y => x.freevars ∪ y.freevars

end Term

-- example (x:String) (α: Finset String) (h:{x : Term | x.closed_under α})
--   (y:Term) (h: y.closed_under α)
-- :
--    by sorry


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

/-
inductive Term --where
| lcons : LTerm → Term                  -- L-constants
| pi                                    -- combinators:     Π
| sigma                                 --                  Σ
| sing                                  -- star constants:  𝔰
| bUnion                                --                  ∪ (binary union)
| iUnion                                --                  ∪ (indexed union)
| var : String → Term                   -- variables
| app : Term → Term → Term              -- application of terms
deriving Repr, DecidableEq

| .Lfunc name args => .Lfunc name (args.map (substitution x replacement))             -- a tirar

-- Definição de substituição de termos: Substituimos _ por _ em _
def substitution (x : String) (replacement : Term) : Term → Term
| .lcons t => .lcons (LTerm.Lsubstitution x replacement t)                                  -- NOT WORKING: replacement teria de ser LTerm
| .var y => if x = y
          then replacement
          else (.var y)
| .app t₁ t₂ => .app (substitution x replacement t₁) (substitution x replacement t₂)  -- funciona? Acho que sim
| t => t                                                                              -- para que pi, sigma, sing, bUnion e iUnion não sejam afetados
decreasing_by sorry             -- TODO (net-ech)

-/

def term_substitution (x : String) (replacement : Term) : Term → Term
| .lcons t => match replacement with
              | .lcons r => .lcons (LTerm.Lsubstitution x r t)                        -- Since replacement has to be an LTerm, we have to add this pattern matching
              | _ => .lcons t
| .var y => if x = y
          then replacement
          else (.var y)
| .app t₁ t₂ => .app (term_substitution x replacement t₁) (term_substitution x replacement t₂)  -- In an application, we do the substitution in each term
| t => t                                                                              -- The combinators Π, Σ and the star constants 𝔰, ∪, ind_⋃ are constants and hence are not affected by substitution



-- TO DO




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

def Formula.freevars : Formula → Finset String
| .L_Form (A : LFormula) => LFormula.Lfreevars_formula A                         --| .L_Form _ => by sorry -- TODO: criar o LFormula.freevars e chamar aqui
| .rel _ ts => Finset.fold (fun x y => x ∪ y) {} Term.freevars ts.toFinset
| .eq a b
| .or a b
| .mem a b => a.freevars ∪ b.freevars
| .not a => a.freevars
| .unbForall x f
| .bForall x t f => f.freevars \ ([x].toFinset)



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

-- ----------------------------
-- SENTENCES (CLOSED FORMULAS)
-- ----------------------------

-- TODO: Este exemplo é o mesmo que temos em FOL
-- Exemplo para calcular as free variables da fórmula R(x,y) ∨ (∀ z Q(z))
def ex_freevars_formula := (rel "R" [var "x", var "y"]) ∨₁ (V₁ "z" (rel "Q" [var "z"]))
#eval Formula.freevars ex_freevars_formula                                  -- The free variables of the formula are the set {x,y}, that is {"x", "y"}


def isClosed (A : Formula) : Prop := Formula.freevars A = {}
def isClosed_check (A : Formula) : Bool := (Formula.freevars A) = {}       -- Prints true or false dependendo se temos var livres ou não

#eval isClosed_check ex_freevars_formula                                    -- Since ex_freevars_formula has x and y as free variables, the output is false
-- TODO: acrescentar um exemplo que dê true

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

/-
inductive Formula : Type
| L_Form : LFormula → Formula
| rel : String → List Term → Formula                              -- R(t₁, ..., tₙ) with R relational symbol of L and t₁,...,tₙ ground terms in L^{omega}_*
| eq : Term → Term → Formula                                      -- t =σ q
| mem : Term → Term → Formula                                     -- t ∈σ q
| not : Formula → Formula                                         -- If A is a formula, then so is (¬A)
| or : Formula → Formula → Formula                                -- If A and B are formulas, then so is (A∨B)
| unbForall (x:String) : Formula → Formula                        -- If A is a base formula, then so is (∀x A)
| bForall : String → Term → Formula → Formula                     -- If A is a formula, then so is (∀x∈t A)


def term_substitution (x : String) (replacement : Term) : Term → Term
| .lcons t => match replacement with
              | .lcons r => .lcons (LTerm.Lsubstitution x r t)                        -- Since replacement has to be an LTerm, we have to add this pattern matching
              | _ => .lcons t
| .var y => if x = y
          then replacement
          else (.var y)
| .app t₁ t₂ => .app (term_substitution x replacement t₁) (term_substitution x replacement t₂)  -- In an application, we do the substitution in each term
| t => t                                                                              -- The combinators Π, Σ and the star constants 𝔰, ∪, ind_⋃ are constants and hence are not affected by substitution


| (L_Form A) => match replacement with
              | (L_Form B) => L_Form (LFormula.Lsubstitution_formula x B A)                        -- Since replacement has to be an LTerm, we have to add this pattern matching
              | _ => (L_Form A)

| (L_Form A) => match replacement with
              | (L_Form B) => L_Form (LFormula.Lsubstitution_formula x replacement A)                        -- Since replacement has to be an LTerm, we have to add this pattern matching
              | _ => (L_Form A)

THIS IS THE NEWER VERSION (18 de julho)
def substitution_formula (x : String) (replacement : Term) : Formula → Formula
| (L_Form A) => L_Form (LFormula.Lsubstitution_formula x replacement A)
| (rel P terms) => rel P (terms.map (term_substitution x replacement))
| (t₁ =₁ t₂) => (term_substitution x replacement t₁) =₁ (term_substitution  x replacement t₂)
| (t₁ ∈₁ t₂) => (term_substitution x replacement t₁) ∈₁ (term_substitution  x replacement t₂)
| (Formula.not A) => ¬₁ (substitution_formula x replacement A)                                                       -- recursivamente em A
| (Formula.or A B) => (substitution_formula x replacement A) ∨₁ (substitution_formula x replacement B)              -- recursivamente em A e B
| (V₁ y A) => if x = y then V₁ y A
              else V₁ y (substitution_formula x replacement A)
| (bV₁ y t A) => if x = y then bV₁ y t A
              else (bV₁ y t (substitution_formula x replacement A))            -- TODO: problema que tbm é preciso substituir no y?


-/


-- TO DO






-- -------------------------------------
-- FORMULA CLOSED UNDER
-- -------------------------------------

/-
inductive Formula : Type
| L_Form : LFormula → Formula
| rel : String → List Term → Formula                              -- R(t₁, ..., tₙ) with R relational symbol of L and t₁,...,tₙ ground terms in L^{omega}_*
| eq : Term → Term → Formula                                      -- t =σ q
| mem : Term → Term → Formula                                     -- t ∈σ q
| not : Formula → Formula                                         -- If A is a formula, then so is (¬A)
| or : Formula → Formula → Formula                                -- If A and B are formulas, then so is (A∨B)
| unbForall (x:String) : Formula → Formula                        -- If A is a base formula, then so is (∀x A)
| bForall : String → Term → Formula → Formula

inductive closed_under : Formula → Finset String → Prop
| cu_L_Form : closed_under (.lcons xs) α
| cu_rel : closed_under (.pi) α
| cu_eq : closed_under (.sigma) α
| cu_mem : closed_under (.sing) α
| cu_not : closed_under (.bUnion) α
| cu_or : closed_under (.iUnion) α
| unbForall :
    x ∈ α →
    -----------
    closed_under (.var x) α
| cu_bForall : closed_under (app t₁ t₂) α               -- is this even right?
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

-- Drei strecher ass gleich, wees net wei dat heescht
inductive Equivalent : Formula → Formula → Prop
| id : Equivalent A A
| comm : Equivalent A B → Equivalent B A
--| nf_left : Equivalent A B → Equivalent (normal_form A) B
--| nf_right : Equivalent A B → Equivalent A (normal_form B)

inductive isTrue : Formula → Prop
| lem : isTrue (A ∨₁ (¬₁A))
-- TODO: Primeiro definir closed_under, depois substition e isto funciona ∀x A(x) → A(t)
-- | substitution {t:Term} {x:String} :
--       x ∈ xs →
--       A.closed_under xs →   -- TODO: definir o closed_under para Formula
--       isTrue (.unbForall x A) →
--       --------------
--       isTrue (Formula.substitution x t A) -- TODO: Definir substituion para Formula

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
| AxS₃ (a f b : Term) : isTrue ((b ∈₁ ((ind_⋃₁·a)·f)) ↔₁ (bE₁ x a (b ∈₁ (f·(var x)))))

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
| (((Σ₁·t₁)·t₂)·t₃) => ((t₁·t₃)·(t₂·t₃))
| ((ind_⋃₁·(𝔰₁·t₁))·t₂) => (t₂·t₁)
| ((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) => ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃))
| t => t

def examplinho (q t : Term) := ((Π₁·q)·t)
--#eval examplinho                                FALTA: falta o REPR que está a dar erro

--notation t "▹" => conv t

--def p₁ : Term := var "p₁"
--def p₂ : Term := var "p₂"

--#eval conv ((Π₁·p₁)·p₂)

-- FALTA: conversions preserve types





/-
Definir um Conv_TypeChecking?

inductive Term_TypeChecking : Term → FType → Prop
| tcLcons (t : LTerm) : Term_TypeChecking (lcons t) G                                                           -- L-constants have type G
| tcPi {σ τ} : Term_TypeChecking pi (σ ⟶ (τ ⟶ σ))                                                             -- Π_{σ,τ} : σ ⟶ (τ ⟶ σ)
| tcSigma {σ τ ρ}: Term_TypeChecking sigma ((σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ)))                           -- Σ_{σ,τ,ρ} : (σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ))
| tcSing {σ}: Term_TypeChecking sing (σ ⟶ σ⋆)                                                                  -- 𝔰_{σ} : σ⋆
| tcBUnion {σ}: Term_TypeChecking bUnion (σ⋆ ⟶ (σ⋆ ⟶ σ⋆))                                                      -- ∪_{σ} : σ⋆ ⟶ (σ⋆ ⟶ σ⋆)
| tcIUnion {σ τ} : Term_TypeChecking iUnion (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆))                                            -- ∪_{σ} : σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆)
| tcVar {x σ}: Term_TypeChecking (var x) σ                                                                       -- Variables x : σ
| tcApp {t₁ t₂ σ τ}: Term_TypeChecking t₁ (σ ⟶ τ) → Term_TypeChecking t₂ σ → Term_TypeChecking (app t₁ t₂) τ    -- If t₁ : (σ ⟶ τ) and t₂ : σ, then t₁t₂ : τ

-- Ex1.4(1). t₁t₂ : τ where t₁ : σ → τ and t₂ : σ
example (σ τ : FType) (t₁ t₂ : Term) (h1: TypeChecking t₁ (σ ⟶ τ)) (h2 : TypeChecking t₂ σ) : TypeChecking (app t₁ t₂) τ :=
  by
    exact TypeChecking.tcApp h1 h2

-- Π₁ : σ⟶τ⟶σ, t₁ : σ  and t₂ : τ, then TypeChecking (conv ((Π₁·t₁)·t₂)) σ
example (σ τ : FType) (t₁ t₂ : Term) (ht₁ : Term_TypeChecking t₁ σ) (ht₂ : Term_TypeChecking t₂ τ) : Term_TypeChecking (conv ((Π₁·t₁)·t₂)) σ := sorry


-/

-- ---------------------
-- REMARK 1.21 (p.26):
-- Conversions preserve types
-- ---------------------


lemma Conv1_TypeChecking (σ τ : FType) (t₁ t₂ : Term) (ht₁ : Term_TypeChecking t₁ σ) (ht₂ : Term_TypeChecking t₂ τ) : Term_TypeChecking (conv ((Π₁·t₁)·t₂)) σ := by
  exact ht₁

lemma Conv2_TypeChecking (σ τ ρ : FType) (t₁ t₂ t₃ : Term) (ht₁ : Term_TypeChecking t₁ (ρ ⟶ σ ⟶ τ)) (ht₂ : Term_TypeChecking t₂ (ρ ⟶ σ)) (ht₃ : Term_TypeChecking t₃ ρ) : Term_TypeChecking (conv ((Σ₁·t₁)·t₂)·t₃) τ := sorry

/-
lemma Conv2_TypeChecking (σ τ ρ : FType) (t₁ t₂ t₃ : Term) (ht₁ : Term_TypeChecking t₁ (ρ ⟶ σ ⟶ τ)) (ht₂ : Term_TypeChecking t₂ (ρ ⟶ σ)) (ht₃ : Term_TypeChecking t₃ ρ) : Term_TypeChecking (conv ((Σ₁·t₁)·t₂)·t₃) τ := by
  exact ht₁

lemma Conv3_TypeChecking (σ τ : FType) (t₁ t₂ : Term) (ht₁ : Term_TypeChecking t₁ σ) (ht₂ : Term_TypeChecking t₂ τ) : Term_TypeChecking (conv ((Π₁·t₁)·t₂)) σ := by
  exact ht₁

lemma Conv4_TypeChecking (σ τ : FType) (t₁ t₂ : Term) (ht₁ : Term_TypeChecking t₁ σ) (ht₂ : Term_TypeChecking t₂ τ) : Term_TypeChecking (conv ((Π₁·t₁)·t₂)) σ := by
  exact ht₁
-/


-- EXAMPLE 1.10 (p.28)





-- PRENEXIFICATION RULES
-- Definir novo inductive para termos as usual prenexification rules?
-- ou usar um isFormula?
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

-- FREE VARIABLES NOT WORKING :'(

end StarLang
