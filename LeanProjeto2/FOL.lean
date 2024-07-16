import LeanProjeto2
import MathLib.Tactic
import Init.Data.String.Basic
import Mathlib.Data.Finset.Basic
import Init.Data.List.Basic


-- import data.string.basic

namespace FOL

-- --------------------
-- CONSTANTES
-- --------------------

-- Variáveis

def LVar : Type := String     -- a tirar

-- Logical connectives (∨ , ¬)

inductive LogCon : Type       -- a tirar
| Ldisj                       -- a tirar
| Lnot                        -- a tirar
| Lforall                     -- a tirar

open LogCon                   -- a tirar

-- --------------------
-- TERMOS String para term
-- --------------------

inductive LTerm : Type
| Lvar : String → LTerm
| Lconst : String → LTerm
| Lfunc : String → List LTerm → LTerm
deriving BEq, Repr

/-
inductive term_is_wellformed2 : List String → LTerm → Prop
| bc :
  x ∈ xs →
  ------------------------------
 term_is_wellformed xs (.Lvar x)
 -/

inductive term_is_wellformed : List String → LTerm → Prop           -- Why do we really need this?
| bc_var :
    (x ∈ xs) →
    term_is_wellformed xs (LTerm.Lvar x)
| bc_const :
    term_is_wellformed xs (LTerm.Lconst c)
| bc_func :
    (∀ t ∈ ts, term_is_wellformed xs t) →
    term_is_wellformed xs (LTerm.Lfunc f ts)


def var_x := LTerm.Lvar "x"
def const_a := LTerm.Lconst "a"
def func_f := LTerm.Lfunc "f" [var_x, const_a]

example : term_is_wellformed ["x", "y"] var_x :=
  term_is_wellformed.bc_var (List.Mem.head _)

-- Example proof of well-formedness for const_a
example : term_is_wellformed ["x", "y"] const_a :=
  term_is_wellformed.bc_const

/-
-- Example proof of well-formedness for func_f   NOT WORKING AINDA
theorem func_f_wellformed : term_is_wellformed ["x", "y"] func_f :=
  term_is_wellformed.bc_func
    (λ t ht =>
      match t with
      | LTerm.Lvar x => term_is_wellformed.bc_var _
      | LTerm.Lconst c => term_is_wellformed.bc_const)
-/


/-
DEFINITION FOR DECIDABLE
-/

mutual
  def decEqTerm : DecidableEq LTerm
    | .Lvar _, .Lconst _
    | .Lconst _, .Lvar _
    | .Lvar _, .Lfunc _ _
    | .Lfunc _ _, .Lvar _
    | .Lfunc _ _, .Lconst _
    | .Lconst _, .Lfunc _ _ => .isFalse fun h => by injection h
    | .Lvar s₁, .Lvar s₂ =>
      if h : s₁ = s₂ then .isTrue (by subst h; rfl)
      else .isFalse fun h => by injection h; contradiction
    | .Lconst s₁, .Lconst s₂ =>
      if h : s₁ = s₂ then .isTrue (by subst h; rfl)
      else .isFalse fun h => by injection h; contradiction
    | .Lfunc s₁ l₁, .Lfunc s₂ l₂ =>
      if h : s₁ = s₂ then
         match decEqListTerm l₁ l₂ with
          | .isTrue t => .isTrue (by subst h; subst t; rfl)
          | isFalse _ => .isFalse fun t => by injection t; contradiction
      else .isFalse fun h => by injection h; contradiction

  def decEqListTerm : DecidableEq (List LTerm)
    | [],[] => .isTrue rfl
    | h::t,[] | [], h::t => .isFalse fun h => by injection h
    | h₁::t₁,h₂::t₂ =>
      match decEqTerm h₁ h₂ with
        | .isTrue h => match decEqListTerm t₁ t₂ with
          | .isTrue t => .isTrue (by subst h₁; subst t; rfl)
          | isFalse _ => .isFalse fun t => by injection t; contradiction
        | isFalse _ => .isFalse fun h => by injection h; contradiction
end

instance : DecidableEq LTerm := decEqTerm
instance : DecidableEq (List LTerm) := decEqListTerm

namespace LTerm

-- Definição de substituição de termos: Substituimos _ por _ em _
def substitution (x : String) (replacement : LTerm) : LTerm → LTerm
| .Lvar y => if x = y
          then replacement
          else (.Lvar y)
| .Lfunc name args => .Lfunc name (args.map (substitution x replacement))
| t => t
decreasing_by sorry             -- TODO (net-ech)

-- Exemplo: substituimos a variável x pela constante a em f(x,a). Output: f(a,a)
#eval substitution "x" const_a func_f
-- #eval substitution var_x const_a func_f CHECK PQ NOT WORKING

-- Definição de variáveis livres num termo (freevars devolve o conjunto das variáveis livres)
def freevars : LTerm → Finset String
| .Lvar s => {s}                                                                      -- Variáveis são livres
| .Lconst _ => {}                                                                     -- Constantes não têm variáveis livres (Não interessa o nome da cst, daí _)
| .Lfunc _ ls => Finset.fold (fun x y => x ∪ y) {} LTerm.freevars (ls.toFinset)       -- Para símbolos funcionais (nome não interessa): ls é a lista dos argumentos (lista de LTerms), vamos recursivamente à procura das free variables
decreasing_by sorry             -- TODO (net-ech)

-- Exemplo: Temos símbolo funcional f aplicado às variáveis x,y e à constante c
def ex_freevars_term := LTerm.Lfunc "f" [LTerm.Lvar "x", LTerm.Lvar "y", LTerm.Lconst "c"]
-- O conjunto das variáveis livres em ex_freevars_term é {x,y}, i.e. {"x", "y"}
#eval freevars ex_freevars_term


end LTerm


-- --------------------
-- FORMULAS
-- --------------------

-- Predicate symbols
def LPred : Type := String                  -- a tirar (fica logo no LFormula)

-- Formulas
inductive LFormula : Type     -- VARIAVEIS
| atomic_L : LPred → List LTerm → LFormula      -- Atomic formulas: recebem um Predicate Symbol e uma lista de termos
| not_L : LFormula → LFormula                   -- Negation
| or_L : LFormula → LFormula → LFormula         -- Disjunction
| forall_L : LVar → LFormula → LFormula         -- Universal quantification

open LFormula

-- Verificamos se uma formula de FOL é atómica
inductive isLAtomic : LFormula → Prop
| at_LForm : isLAtomic (atomic_L x l_LTerm)


namespace LFormula

-- Define a set to store free variables
-- Define a set to store free variables
def freevars_formula : LFormula → Finset String
| (LFormula.atomic_L _ ts) =>
  let term_freevars : List (Finset String) := List.map LTerm.freevars ts;
  let all_freevars : Finset String := term_freevars.foldl (λ acc fvs => acc ∪ fvs) {};
  all_freevars
| (LFormula.not_L A) => freevars_formula A
| (LFormula.or_L A B) => freevars_formula A ∪ freevars_formula B
| (LFormula.forall_L _ A) => freevars_formula A

-- Define a simple formula for testing
def formula_example := LFormula.or_L (LFormula.atomic_L "P" [LTerm.Lvar "x", LTerm.Lvar "y"])
                                    (LFormula.forall_L "z" (LFormula.atomic_L "Q" [LTerm.Lvar "y"]))

-- Evaluate the free variables of the formula
#eval freevars_formula formula_example
-- Expected Output: {"x", "y"}








def freevars : LFormula → Finset String
| _ => {} -- TODO


def isClosed (f:LFormula) : Prop := f.freevars = {}

end LFormula

notation "¬₀" A => not_L A
notation A "∨₀" B => or_L A B
notation "∀₀" => forall_L

-- ----------------------------
-- ABREVIATURAS PARA ∧, →, ∃, ↔
-- ----------------------------

-- Conjunction:  A ∧ B := ¬(¬A∨¬B)
def and_L (A B : LFormula) : LFormula :=
  ¬₀ ((¬₀ A) ∨₀ (¬₀ B))

-- Implication:  A → B := ¬ A ∨ B
def implies_L (A B : LFormula) : LFormula :=
  (¬₀ A) ∨₀ B

notation A "∧₀" B => and_L A B
notation A "→₀" B => implies_L A B

-- Equivalence:  A ↔ B := (A → B) ∧ (B → A)
def iff_L (A B : LFormula) : LFormula :=
  (A →₀ B) ∧₀ (B →₀ A)

-- Existential quantification:  ∃x A := ¬ (∀x (¬ A))
def exists_L (x : LVar) (A : LFormula) : LFormula :=
  ¬₀ (∀₀ x (¬₀ A))
-- not_L (forall_L x (not_L A))

notation A "↔₀" B => iff_L A B
notation "∃₀" x A => exists_L x A
--def ∃₀ := exists_L

-- ∃x A := ¬ (∀x (¬ A))                                -- NOT WORKING
-- def lexists (x : LVar) (φ : LFormula) : LFormula :=
--  ¬₀ (∀₀ x (¬₀ φ))
