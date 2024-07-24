import LeanProjeto2
import MathLib.Tactic
import Init.Data.String.Basic
import Mathlib.Data.Finset.Basic
import Init.Data.List.Basic


-- import data.string.basic

namespace FOL

-- --------------------
-- TERMOS String para term
-- --------------------

inductive LTerm : Type
| Lvar : String → LTerm
| Lconst : String → LTerm
| Lfunc : String → List LTerm → LTerm
deriving BEq, Repr

open LTerm

-- Definition: well-formed terms
inductive LTerm_is_wellformed : List String → LTerm → Prop
| bc_var : (x ∈ xs) → LTerm_is_wellformed xs (Lvar x)                                     -- A variable Lvar x is well-formed if x is in the list
| bc_const : LTerm_is_wellformed xs (Lconst c)                                            -- A constant is always well-formed
| bc_func : (∀ t ∈ ts, LTerm_is_wellformed xs t) → LTerm_is_wellformed xs (Lfunc f ts)    -- If t₁,...,tₙ are well-formed, then so is f(t₁,...,tₙ)


def var_x := Lvar "x"
def const_a := Lconst "a"
def func_f := Lfunc "f" [var_x, const_a]

-- Example: proof that var_x is well-formed
example : LTerm_is_wellformed ["x", "y"] var_x :=
  LTerm_is_wellformed.bc_var (List.Mem.head _)

-- Example proof that const_a is well-formed
example : LTerm_is_wellformed ["x", "y"] const_a :=
  LTerm_is_wellformed.bc_const

/-
-- Example proof of well-formedness for func_f   NOT WORKING AINDA
theorem func_f_wellformed : LTerm_is_wellformed ["x", "y"] func_f :=
  LTerm_is_wellformed.bc_func
    (λ t ht =>
      match t with
      | LTerm.Lvar x => LTerm_is_wellformed.bc_var _
      | LTerm.Lconst c => LTerm_is_wellformed.bc_const)
-/


-- Definition: permite associar um conjunto de variáveis a um termo (para lidarmos com coisas como t(x) em axiomas, etc)
inductive L_closed_under_term : LTerm → Finset String → Prop
| Lcu_Lvar : x ∈ α → L_closed_under_term (Lvar x) α                   -- A variables (Lvar x) is closed under the set of variables α if x is an element of α.
| Lcu_Lconst : L_closed_under_term (Lconst c) α                       -- A constant (Lconst c) is closed under any set of variables α since constants do not contain any variables.
| Lcu_Lfunc :
    (∀ t, t ∈ ts → L_closed_under_term t α) →                         -- A function term (Lfunc f ts) is closed under α if every term t in the list ts is closed under α.
    L_closed_under_term (Lfunc f ts) α
-- TODO: tem de ser sempre o mesmo conjunto α? Em princípio cada t podia ter outro conjunto...

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
| forall_L : String → LFormula → LFormula         -- Universal quantification
-- deriving BEq, Repr NOT WORKING

open LFormula

-- Verificamos se uma formula de FOL é atómica
inductive isLAtomic : LFormula → Prop
| at_LForm : isLAtomic (atomic_L x l_LTerm)


-- Definition: well-formed formulas
inductive LFormula_is_wellformed : List String → LFormula → Prop
| wf_atomic {xs P ts} :
    (∀ t ∈ ts, LTerm_is_wellformed xs t) →
    LFormula_is_wellformed xs (atomic_L P ts)                -- If t₁,...,tₙ are well-formed terms, then so is P(t₁,...,tₙ)
| wf_not {xs A} :
    LFormula_is_wellformed xs A →
    LFormula_is_wellformed xs (not_L A)                      -- If A is a well-formed formula, then so is ¬A.
| wf_or {xs A B} :
    LFormula_is_wellformed xs A →
    LFormula_is_wellformed xs B →
    LFormula_is_wellformed xs (or_L A B)                     -- If A and B are well-formed formulas, then so is A∨B.
| wf_forall {xs x A} :
    LFormula_is_wellformed (x :: xs) A →
    LFormula_is_wellformed xs (forall_L x A)                 -- If A is a well-formed formula (for our list xs and the bound variable x), then so is ∀x A.


-- Definition: permite associar um conjunto de variáveis a uma fórmula (para lidarmos com coisas como t(x) em axiomas, etc)
inductive L_closed_under_formula : LFormula → Finset String → Prop  -- TODO: change descripts here
| cu_atomic_L : ∀ (P : LPred) (ts : List LTerm) (α : Finset String),        -- An atomic formula atomic_L P ts is closed under a set α if all terms in the list ts are closed under α
    (∀ t, t ∈ ts → L_closed_under_term t α) →
    L_closed_under_formula (atomic_L P ts) α
| cu_not_L : ∀ (A : LFormula) (α : Finset String),                          -- The negation ¬₀A is closed under a set α if A is closed under α.
    L_closed_under_formula A α →
    L_closed_under_formula (not_L A) α
| cu_or_L : ∀ (A B : LFormula) (α β : Finset String),                       -- The disjuction A∨₀B is closed under a union of two sets α and β if A is closed under α and B is closed under β.
    L_closed_under_formula A α →
    L_closed_under_formula B β →
    L_closed_under_formula (or_L A B) (α ∪ β)
| cu_forall_L : ∀ (x : String) (A : LFormula) (α : Finset String),          -- ∀₀ x A is closed under a set α if A is closed under the set α with the variable x added to it.
    L_closed_under_formula A (α ∪ {x}) →
    L_closed_under_formula (forall_L x A) (α ∪ {x})       -- TODO: check this with the ∪ {x}

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
def exists_L (x : String) (A : LFormula) : LFormula :=
  ¬₀ (V₀ x (¬₀ A))
-- not_L (forall_L x (not_L A))

notation A "↔₀" B => iff_L A B
notation "∃₀" => exists_L

-- ----------------------------
-- FREE VARIABLES IN FORMULAS
-- ----------------------------

-- Definition: free variables of formulas in L (a set that stores free variables)
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

def isClosed_L (A : LFormula) : Prop := A.Lfreevars_formula = {}
def isClosed_L_check (A : LFormula) : Bool := (Lfreevars_formula A) = {}       -- Prints true or false dependendo se temos var livres ou não

#eval isClosed_L_check ex_Lfreevars_formula                                    -- Since ex_Lfreevars_formula has x and y as free variables, the output is false


-- ----------------------------
-- SUBSTITUTION FOR FORMULAS
-- ----------------------------

def Lsubstitution_formula (x : String) (replacement : LTerm) : LFormula → LFormula
| (atomic_L pred terms) => atomic_L pred (terms.map (Lsubstitution x replacement))                           -- substituimos em cada termo da formula atomica
| (¬₀ A) => ¬₀ (Lsubstitution_formula x replacement A)                                                       -- recursivamente em A
| (A ∨₀ B) => (Lsubstitution_formula x replacement A) ∨₀ (Lsubstitution_formula x replacement B)              -- recursivamente em A e B
| (V₀ y A) => if x = y then V₀ y A
              else V₀ y (Lsubstitution_formula x replacement A)

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
