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
DEFINITION FOR DECIDABLE (for terms)
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
def Lsubstitution (x : String) (replacement : LTerm) : LTerm → LTerm
| .Lvar y => if x = y
          then replacement
          else (.Lvar y)
| .Lfunc name args => .Lfunc name (args.map (Lsubstitution x replacement))
| t => t
decreasing_by sorry             -- TODO (net-ech)

-- Exemplo: substituimos a variável x pela constante a em f(x,a). Output: f(a,a)
#eval Lsubstitution "x" const_a func_f
-- #eval Lsubstitution var_x const_a func_f CHECK PQ NOT WORKING

-- Definição de variáveis livres num termo (Lfreevars devolve o conjunto das variáveis livres)
def Lfreevars : LTerm → Finset String
| .Lvar s => {s}                                                                        -- Variáveis são livres
| .Lconst _ => {}                                                                       -- Constantes não têm variáveis livres (Não interessa o nome da cst, daí _)
| .Lfunc _ ls => Finset.fold (fun x y => x ∪ y) {} LTerm.Lfreevars (ls.toFinset)        -- Para símbolos funcionais (nome não interessa): ls é a lista dos argumentos (lista de LTerms), vamos recursivamente à procura das free variables
decreasing_by sorry             -- TODO (net-ech)

-- Exemplo: Temos símbolo funcional f aplicado às variáveis x,y e à constante c
def ex_Lfreevars_term := LTerm.Lfunc "f" [LTerm.Lvar "x", LTerm.Lvar "y", LTerm.Lconst "c"]
-- O conjunto das variáveis livres em ex_Lfreevars_term é {x,y}, i.e. {"x", "y"}
#eval Lfreevars ex_Lfreevars_term

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
-- deriving BEq, Repr NOT WORKING

open LFormula

-- Verificamos se uma formula de FOL é atómica
inductive isLAtomic : LFormula → Prop
| at_LForm : isLAtomic (atomic_L x l_LTerm)

namespace LFormula

-- ----------------------------
-- NOTAÇÕES PARA ¬, ∨, ∀
-- ----------------------------

notation "¬₀" A => not_L A
notation A "∨₀" B => or_L A B
notation "V₀" => forall_L

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
  ¬₀ (V₀ x (¬₀ A))
-- not_L (forall_L x (not_L A))

notation A "↔₀" B => iff_L A B
notation "∃₀" => exists_L

-- ----------------------------
-- FREE VARIABLES IN FORMULAS
-- ----------------------------

-- Define a set to store free variables
def Lfreevars_formula : LFormula → Finset String
| (LFormula.atomic_L _ ts) =>                                                                 -- Gives the union of the free variables of each term in the term list ts.
  let term_Lfreevars : List (Finset String) := List.map LTerm.Lfreevars ts;
  let all_Lfreevars : Finset String := term_Lfreevars.foldl (λ acc fvs => acc ∪ fvs) {};
  all_Lfreevars
| (¬₀ A) => Lfreevars_formula A                                                                -- The free variables of ¬A are the same as those of A.
| (A ∨₀ B) => Lfreevars_formula A ∪ Lfreevars_formula B                                         -- The free variables of A ∨ B are the union of the free variables of A and the free variables of B.
| (V₀ x A) => Lfreevars_formula A \ {x}                                                        -- The free variables of ∀x A are the free variables of A except for the variable x.

open LTerm

-- Exemplo para calcular as free variables da fórmula P(x,y) ∨ (∀ z Q(z))
def ex_Lfreevars_formula := (atomic_L "P" [Lvar "x", Lvar "y"]) ∨₀ (V₀ "z" (atomic_L "Q" [Lvar "z"]))
#eval Lfreevars_formula ex_Lfreevars_formula                                  -- The free variables of the formula are the set {x,y}, that is {"x", "y"}

-- ----------------------------
-- SENTENCES (CLOSED FORMULAS)
-- ----------------------------

def isClosed (A : LFormula) : Prop := A.Lfreevars_formula = {}
def isClosed_check (A : LFormula) : Bool := (Lfreevars_formula A) = {}       -- Prints true or false dependendo se temos var livres ou não

#eval isClosed_check ex_Lfreevars_formula                                    -- Since ex_Lfreevars_formula has x and y as free variables, the output is false


-- ----------------------------
-- SUBSTITUTION FOR FORMULAS
-- ----------------------------

def Lsubstitution_formula (x : String) (replacement : LTerm) : LFormula → LFormula
| (atomic_L pred terms) => atomic_L pred (terms.map (Lsubstitution x replacement))                           -- substituimos em cada termo da formula atomica
| (¬₀ A) => ¬₀ (Lsubstitution_formula x replacement A)                                                       -- recursivamente em A
| (A ∨₀ B) => (Lsubstitution_formula x replacement A) ∨₀ (Lsubstitution_formula x replacement B)              -- recursivamente em A e B
| (V₀ y A) => if x = y then V₀ y A     -- If x is the same as the bound variable y, we don't substitute inside the quantifier
              else V₀ y (Lsubstitution_formula x replacement A)  -- If x is different from the bound variable y, we perform the Lsubstitution inside the quantifier

-- Example
def ex_formula : LFormula :=
    (atomic_L "P" [Lvar "x", Lvar "y"]) ∨₀ (V₀ "z" (atomic_L "Q" [Lvar "z"]))

def example_Lsubstitution := Lsubstitution_formula "x" (LTerm.Lconst "a") ex_formula               -- substitui a variável x pela constante a em ex_formula

-- #eval example_Lsubstitution     PRECISAMOS DE REPR, mas para isso precisamos de decidable para formulas

-- ----------------------------
-- TERM FREE FOR A VARIABLE IN A FORMULA
-- ----------------------------

-- Verifica if a variable x is bound in a formula A
def is_bound (x : String) : LFormula → Bool
| (atomic_L _ _) => false
| (¬₀ A) => is_bound x A
| (A ∨₀ B) => is_bound x A || is_bound x B
| (V₀ y A) => x = y || is_bound x A

-- Verifica if a term t is free for a variable x in a formula A
def is_free_for (t : LTerm) (x : String) : LFormula → Bool
| (atomic_L _ ts) =>
  Lfreevars t ∩ Lfreevars_formula (atomic_L "" ts) = ∅
| (¬₀ A) => is_free_for t x A
| (A ∨₀ B) => is_free_for t x A && is_free_for t x B
| (V₀ y A) =>
  if x = y then
    Lfreevars t ∩ Lfreevars_formula (V₀ y A) = ∅
  else
    is_free_for t x A

-- Example formula
def ex_formula2 := (V₀ "x" (atomic_L "P" [Lvar "x"])) ∨₀ (atomic_L "Q" [Lvar "x", Lvar "y"])

-- Check if term "y" is free for "x" in the example formula
def ex_formula2_check := is_free_for (LTerm.Lvar "y") "x" ex_formula2

#eval ex_formula2_check  -- vai dar false


end LFormula
