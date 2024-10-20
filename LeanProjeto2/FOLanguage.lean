import MathLib.Tactic
import Init.Data.String.Basic
import Mathlib.Data.Finset.Basic
import Init.Data.List.Basic
import Mathlib.Data.List.Basic
import Batteries

open Batteries

-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
--                    FOL (versão COM tuplos)
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------


-- --------------------------------
-- --------------------------------
--              TERMS
-- --------------------------------
-- --------------------------------

inductive LTerm : Type
| Lvar : String → LTerm
| Lconst : String → LTerm
| Lfunc : String → List LTerm → LTerm
deriving BEq, Repr

open LTerm

-- EXAMPLE: some terms in FOL to use in future examples
def Lvar_x := Lvar "x"
def Lvar_y := Lvar "y"
def Lvar_z := Lvar "z"
def Lconst_a := Lconst "a"
def Lconst_k := Lconst "k"
def Lfunc_f := Lfunc "f" [Lvar_x, Lconst_a]
def Lfunc_g := Lfunc "g"

-- --------------------------------
-- TERMS OF TUPLES (new)
-- --------------------------------

--inductive LTermTuple
--| Ltt : Finset LTerm → LTermTuple

def LTermTuple := List LTerm
deriving BEq, Repr

def LTermTuple2 := Finset LTerm

-- This function takes a list of LTerm and makes a term tuple out of it
def makeLTuple (ts : List LTerm) : LTermTuple := ts

-- We define a function in order to access any element in the tuple
def getLElement (n : Nat) (t : LTermTuple) : Option LTerm :=           -- Option para ter some/none para o caso do tuple ter 2 elementos e pedirmos o terceiro
  List.get? t n

-- -------
-- EXAMPLE: a tuple of terms + access to its elements (new)
-- -------

def exLTermTuple : LTermTuple := makeLTuple ([(Lvar_x), Lconst_a])  -- a tuple of terms (a list with the terms x and a)

def exLFirstElement := getLElement 0 exLTermTuple
def exLSecondElement := getLElement 1 exLTermTuple
def exLThirdElement := getLElement 2 exLTermTuple
#eval exLFirstElement
#eval exLSecondElement
#eval exLThirdElement

-- --------------------------------
-- WELL-FORMED TERMS
-- --------------------------------

-- Definition: well-formed terms
inductive LTerm_is_wellformed : List String → LTerm → Prop
| bc_var : (x ∈ xs) → LTerm_is_wellformed xs (Lvar x)                                     -- A variable Lvar x is well-formed if x is in the list
| bc_const : LTerm_is_wellformed xs (Lconst c)                                            -- A constant is always well-formed
| bc_func : (∀ t ∈ ts, LTerm_is_wellformed xs t) → LTerm_is_wellformed xs (Lfunc f ts)    -- If t₁,...,tₙ are well-formed, then so is f(t₁,...,tₙ)

-- Definition: well-formed tuple of terms (new)
inductive LTermTuple_is_wellformed : List String → List LTerm → Prop
| bc_tuple : (∀ t ∈ ts, LTerm_is_wellformed xs t) → (LTermTuple_is_wellformed xs ts)

-- --------
-- Example:
-- --------

-- The variable Lvar_x is well-formed
lemma exA : LTerm_is_wellformed ["x", "y"] Lvar_x :=
  LTerm_is_wellformed.bc_var (List.Mem.head _)

lemma exB : LTerm_is_wellformed ["x", "y"] Lvar_y :=
  LTerm_is_wellformed.bc_var (by simp [Lvar_y])

-- The constant Lconst_a is well-formed (constants are inherently well-formed)
example : LTerm_is_wellformed ["x", "y"] Lconst_a :=
  LTerm_is_wellformed.bc_const



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



def LTerm.subst (t : LTerm) (substitutions : HashMap String LTerm) : LTerm :=
match t with
  | Lvar n => substitutions.findD n (Lvar n)
  | Lconst c => Lconst c
  | Lfunc f args => Lfunc f (args.map (fun t => subst t substitutions))
decreasing_by sorry             -- TBD (net-ech)


-- Definição de substituição de termos: Substituimos _ por _ em _
def Lsubstitution (x : String) (replacement : LTerm) : LTerm → LTerm
| .Lvar y => if x = y
          then replacement
          else (.Lvar y)
| .Lfunc name args => .Lfunc name (args.map (Lsubstitution x replacement))
| t => t
decreasing_by sorry             -- TBD (net-ech)

-- Definição de substituição de tuple terms: Substituimos _ por _ em _ (new)
def LsubstitutionTuple (x : String) (replacement : LTerm) : LTermTuple → LTermTuple
| [] => []
| (t :: ts) => (Lsubstitution x replacement t) :: LsubstitutionTuple x replacement ts


-- --------
-- Example: substitution in terms and tuple of terms
-- --------

-- substituimos a variável x pela constante a em f(x,a). Output: f(a,a)
#eval Lsubstitution "x" Lconst_a Lfunc_f
#eval LsubstitutionTuple "x" Lconst_a [Lfunc_f]   -- does the same job as Lsubstitution when the list has only one element

-- substituimos a variável x pela constante a em [ x,a ]. Output: [ a,a ]
def exTuple := [Lvar_x, Lconst_a]
#eval LsubstitutionTuple "x" Lconst_a exTuple


-- ---------------------------------------
-- (FREE) VARIABLES IN A TERM
-- ---------------------------------------

-- DEFINITION: (free) variables in terms
--             (Lfreevars returns the set of (free) variables)
def Lfreevars : LTerm → Finset String
| .Lvar s => {s}                                                                        -- Variáveis são livres
| .Lconst _ => {}                                                                       -- Constantes não têm variáveis livres (Não interessa o nome da cst, daí _)
| .Lfunc _ ls => Finset.fold (fun x y => x ∪ y) {} Lfreevars (ls.toFinset)        -- Para símbolos funcionais (nome não interessa): ls é a lista dos argumentos (lista de LTerms), vamos recursivamente à procura das free variables
decreasing_by sorry             -- TODO (net-ech)

-- DEFINITION: (free) variables in tuples of terms              (new)
--             (Lfreevars returns the set of (free) variables)
def LfreevarsTuple (tuple : LTermTuple) : Finset String :=
  (tuple.map Lfreevars).foldl (fun acc fv => acc ∪ fv) ∅

/-
tuple.map Lfreevars:
    cria uma lista de Finset String em que cada elemento
    é o conjunto das var livres para um termo no tuplo
foldl:
    fold/combinamos a lista de conjuntos no só Finset.
    Precisamos de algo que acumula (acc) e o conjunto atual que temos (fv).
    Depois juntos usando a união de acc e fv.
    Usamos o conjunto vazio ∅ para valor inicial para o acc.
-/

-- --------
-- Example: termo f(x,y,c) tem x e y como variáveis livres (símbolo funcional f aplicado às variáveis x,y e à constante c)
-- --------

def ex_Lfreevars_term := LTerm.Lfunc "f" [Lvar_x, Lvar_y, Lconst_a]
def ex_Lfreevars_tuple := [Lvar_x, Lconst_a, LTerm.Lfunc "g" [Lvar_y]]

-- O conjunto das variáveis livres em ex_Lfreevars_term é {x,y}, i.e. {"x", "y"}
#eval Lfreevars ex_Lfreevars_term          -- Output: {"x", "y"}
#eval LfreevarsTuple ex_Lfreevars_tuple    -- Output: {"x", "y"}

-- ---------------------------------------
-- CLOSED TERMS
-- ---------------------------------------

-- DEFINITION: Closed term (a term without free variables)
def isClosedTerm_L (t : LTerm) : Prop := Lfreevars t = {}
def isClosedTerm_L_check (t : LTerm) : Bool := Lfreevars t = {}       -- Prints true or false dependendo se temos var livres ou não

-- (new)
def isClosedTupleTerm_L (t : LTermTuple) : Prop := LfreevarsTuple t = {}
def isClosedTupleTerm_L_check (t : LTermTuple) : Bool := (LfreevarsTuple t) = {}

-- --------
-- EXAMPLE: TERMS
-- --------
-- Exemplo: termo f(x,y,c) tem x e y como variáveis, logo não é fechado
#eval isClosedTerm_L_check ex_Lfreevars_term
-- Exemplo: term a (constante) não tem variáveis, logo é fechado
#eval isClosedTerm_L_check Lconst_a

-- --------
-- EXAMPLE: TUPLE TERMS (new)
-- --------
#eval isClosedTupleTerm_L_check ex_Lfreevars_tuple
#eval isClosedTupleTerm_L_check [Lvar_x, Lconst_k, Lfunc_g [Lvar_y, Lvar_z]]

-- Outro exemplo
def ex_Lterm_tuple := [Lconst_k, Lfunc_g [Lconst_a]]
#eval isClosedTupleTerm_L_check ex_Lterm_tuple


-- --------------------------------
-- --------------------------------
--            FORMULAS
-- --------------------------------
-- --------------------------------

-- Formulas
inductive LFormula : Type
| atomic_L : String → List LTerm → LFormula      -- Atomic formulas: recebem um Predicate Symbol e uma lista de termos
| not_L : LFormula → LFormula                    -- Negation
| or_L : LFormula → LFormula → LFormula          -- Disjunction
| forall_L : String → LFormula → LFormula        -- Universal quantification
deriving BEq, Repr




-- Convertemos a lista de variáveis numa nested sequence de quantificadores `forall_L`
def forallTuple_L (vars : List String) (A : LFormula) : LFormula :=
  vars.foldr (fun v acc =>
    LFormula.forall_L v acc
  ) A

-- -------
-- Example
-- -------

-- We define the formula `P(x, y)`
def exFormula : LFormula :=
  LFormula.atomic_L "P" [Lvar_x, Lvar_y]

-- We now define the formula `forall x (forall y P(x, y))` by using the forallTuple_L
def forall_exFormula : LFormula :=
  forallTuple_L ["x", "y"] exFormula

#eval forall_exFormula    -- Output: ∀x (∀y P(x,y))

-- -------------------------------------------------

open LFormula

-- ------------------------
-- Atomic formulas
-- ------------------------

-- ATOMIC FORMULAS:
-- Verificamos se uma formula de FOL é atómica
inductive isLAtomic : LFormula → Prop
| at_LForm : isLAtomic (atomic_L x l_LTerm)

-- Verificamos se uma formula de FOL é atómica ou não
def isLAtomic_check (f : LFormula) : Bool :=
  match f with
  | atomic_L _ _ => true
  | _ => false

-- --------
-- EXAMPLE:
-- --------
def term_x := LTerm.Lvar "x"
def term_y := LTerm.Lvar "y"
def exFormulaAt : LFormula := LFormula.atomic_L "P" [term_x, term_y]
def exNotFormulaAt : LFormula := LFormula.not_L exFormulaAt
#eval isLAtomic_check exFormulaAt       -- Output: true
#eval isLAtomic_check exNotFormulaAt    -- Output: false

-- -------------------------------------------------

-- ---------------------------
-- WELL-FORMED FORMULAS
-- ---------------------------

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

-- -------------------------------------------------


-- ----------------------------
-- NOTAÇÕES PARA ¬, ∨, ∀
-- ----------------------------

notation "¬₀" A => not_L A
notation A "∨₀" B => or_L A B
notation "∀₀₀" => forall_L                        -- Perguntar: notação
notation "∀₀" => forallTuple_L

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

-- Existential quantification (for one variable):  ∃x A := ¬ (∀x (¬ A))
def exists_L (x : String) (A : LFormula) : LFormula :=
  ¬₀ (∀₀₀ x (¬₀ A))

-- Existential quantification (for one variable):  ∃x A := ¬ (∀x (¬ A))
def existsTuple_L (x : List String) (A : LFormula) : LFormula :=
  ¬₀ (∀₀ x (¬₀ A))

notation A "↔₀" B => iff_L A B
notation "∃₀₀" => exists_L
notation "∃₀" => existsTuple_L

-- ----------------------------
-- FREE VARIABLES IN FORMULAS
-- ----------------------------

-- DEFINITION: free variables of formulas in L (a set that stores free variables)
def Lfreevars_formula : LFormula → Finset String
| (LFormula.atomic_L _ ts) =>                                                                  -- Gives the union of the free variables of each term in the term list ts.
  let term_Lfreevars : List (Finset String) := List.map Lfreevars ts;
  let all_Lfreevars : Finset String := term_Lfreevars.foldl (λ acc fvs => acc ∪ fvs) {};
  all_Lfreevars
| (¬₀ A) => Lfreevars_formula A                                                                -- The free variables of ¬A are the same as those of A.
| (A ∨₀ B) => Lfreevars_formula A ∪ Lfreevars_formula B                                        -- The free variables of A ∨ B are the union of the free variables of A and the free variables of B.
| (∀₀₀ x A) => Lfreevars_formula A \ {x}

-- (new)
def Lfreevars_forallTuple (xs : List String) (A : LFormula) : Finset String :=
  Lfreevars_formula A \ xs.toFinset

-- --------
-- EXAMPLE:
-- --------

def example_formula := ∀₀ ["x", "y"] (atomic_L "P" [Lvar_x, Lvar_z])

#eval Lfreevars_forallTuple ["x", "y"] (atomic_L "P" [Lvar_x, Lvar_z])   -- Output: {"z"}
#eval Lfreevars_formula (∀₀ ["x", "y"] (atomic_L "P" [Lvar_x, Lvar_z]))  -- Output: {"z"}

-- ----------------------------
-- VARIABLES IN FORMULAS
-- ----------------------------

-- DEFINITION: all the variables of a formula in L
def Lallvars_formula : LFormula → Finset String
| (LFormula.atomic_L _ ts) =>
  let term_Lallvars : List (Finset String) := List.map Lfreevars ts;
  let all_Lallvars : Finset String := term_Lallvars.foldl (λ acc fvs => acc ∪ fvs) {};
  all_Lallvars
| (¬₀ A) => Lallvars_formula A
| (A ∨₀ B) => Lallvars_formula A ∪ Lallvars_formula B
| (∀₀₀ x A) => Lallvars_formula A ∪ {x}                                -- Here we guarantee to include the bound variable x

-- --------
-- EXAMPLE:
-- --------

-- Exemplo para calcular as free variables da fórmula (∀ z Q(z))
def ex_Lfreevars_atFormula := (∀₀₀ "z" (atomic_L "Q" [Lvar_z]))
#eval Lfreevars_formula ex_Lfreevars_atFormula

-- Exemplo para calcular as free variables da fórmula P(x,y) ∨ (∀ z Q(z))
def ex_Lfreevars_formula := (atomic_L "P" [Lvar_x, Lvar_y]) ∨₀ (∀₀₀ "z" (atomic_L "Q" [Lvar_z]))
#eval Lfreevars_formula ex_Lfreevars_formula                                  -- The free variables of the formula are the set {x,y}, that is {"x", "y"}

-- Exemplo para calcular as free variables da fórmula P(x,y) ∨ (∀ {x,z} Q(x,z))
def ex_LfreevarsTuple_formula := (atomic_L "P" [Lvar_x, Lvar_y]) ∨₀ (∀₀ {"x","z"} (atomic_L "Q" [Lvar_x,Lvar_z]))
#eval Lfreevars_formula ex_LfreevarsTuple_formula


-- ----------------------------
-- SENTENCES (CLOSED FORMULAS)
-- ----------------------------

def isClosed_L (A : LFormula) : Prop := Lfreevars_formula A = {}
def isClosed_L_check (A : LFormula) : Bool := (Lfreevars_formula A) = {}       -- Prints true or false dependendo se temos var livres ou não

#eval isClosed_L_check ex_Lfreevars_atFormula       -- Output: true
#eval isClosed_L_check ex_Lfreevars_formula         -- Output: false                         -- Since ex_Lfreevars_formula has x and y as free variables, the output is false
#eval isClosed_L_check ex_LfreevarsTuple_formula    -- Output: false

-- ----------------------------
-- SUBSTITUTION FOR FORMULAS
-- ----------------------------

-- DEFINITION: Lsubstitution in formulas
def Lsubstitution_formula (x : String) (replacement : LTerm) : LFormula → LFormula
| (atomic_L pred terms) => atomic_L pred (terms.map (Lsubstitution x replacement))                           -- substituimos em cada termo da formula atomica
| (¬₀ A) => ¬₀ (Lsubstitution_formula x replacement A)                                                       -- recursivamente em A
| (A ∨₀ B) => (Lsubstitution_formula x replacement A) ∨₀ (Lsubstitution_formula x replacement B)              -- recursivamente em A e B
| (∀₀₀ y A) => if x = y then ∀₀₀ y A
              else ∀₀₀ y (Lsubstitution_formula x replacement A)


-- Mudança: acrescentar simultaneous substitution?
def LFormula.subst (f:LFormula) (subs:HashMap String LTerm) : LFormula := match f with
  | .atomic_L s ts => LFormula.atomic_L s (ts.map (fun x => LTerm.subst x subs))
  | .not_L f => .not_L (LFormula.subst f subs)
  | .or_L f1 f2 => .or_L (LFormula.subst f1 subs) (LFormula.subst f2 subs)
  | .forall_L s f => .forall_L s (LFormula.subst f (subs.erase s))


-- DEFINITION: Lsubstitution for tuples in formulas
-- substituição em cada termo do tuplo e depois tomar a substituição na formula onde aparecem os termos
def LsubstitutionTuple_formula (x : String) (replacement : LTerm) (TermTuple : LTermTuple) : LFormula → LFormula
| (atomic_L pred formula_terms) => atomic_L pred (formula_terms.map (Lsubstitution x replacement))
| (¬₀ A) => ¬₀ (LsubstitutionTuple_formula x replacement TermTuple A)
| (A ∨₀ B) => (LsubstitutionTuple_formula x replacement TermTuple A) ∨₀ (LsubstitutionTuple_formula x replacement TermTuple B)
| (∀₀₀ y A) => if x = y then ∀₀₀ y A
              else ∀₀₀ y (LsubstitutionTuple_formula x replacement TermTuple A)

-- --------
-- Example: simples
-- --------
def ex_formula : LFormula :=
    (atomic_L "P" [Lvar "x", Lvar "y"]) ∨₀ (∀₀₀ "z" (atomic_L "Q" [Lvar "z"]))

def example_Lsubstitution := Lsubstitution_formula "x" (Lconst_a) ex_formula       -- substitui a variável x pela constante a em ex_formula

#eval example_Lsubstitution

-- --------
-- Example: tuplos
-- --------

-- Another example: Atomic formula P(x,y)
def exSubstTupleFormula := atomic_L "P" [Lvar_x, Lvar_y]
-- Substituir o 'x' pelo 'a' no tuplo {x,y} na fórmula P(x,y)
#eval LsubstitutionTuple_formula "x" (Lconst_a) [Lvar_x, Lvar_y] exSubstTupleFormula -- P[ a,y ]
-- aplica a substituição (substituir x por a) em cada termo do tuplo {x,y} e aplica o resultado na formula
-- -- substitui x por a em Lvar_x (fica a); substitui x por a em Lvar_y (fica y); no final P(x,y) fica P(a,x)

-- A definição LsubstitutionTuple_formula também funciona para o caso Lsubstitution_formula
#eval LsubstitutionTuple_formula "x" (Lconst_a) [Lvar_x] ex_formula


-- -------------------------------------
-- BOUND VARIABLES
-- -------------------------------------

-- Verifica if a variable x is bound in a formula A
def is_bound (x : String) : LFormula → Bool
| (atomic_L _ _) => false
| (¬₀ A) => is_bound x A
| (A ∨₀ B) => is_bound x A || is_bound x B
| (∀₀₀ y A) => x = y || is_bound x A

def is_bound_list (vars : List String) : LFormula → Bool
| (atomic_L _ _) => vars.all (fun _ => false)     -- Atomic formulas don't have bound variables
| (¬₀ A) => is_bound_list vars A
| (A ∨₀ B) => is_bound_list vars A || is_bound_list vars B
| (∀₀₀ y A) => vars.all (fun x => x = y) || is_bound_list vars A
-- Last: Checks if each variable in the list is either equal to the bound variable or is bounded in A

-- --------
-- Example: the variable x is bound in the formula, while the variable y is not
-- --------
#eval is_bound "x" ((∀₀₀ "x" (atomic_L "P" [Lvar_x])) ∨₀ (atomic_L "Q" [Lvar_x, Lvar_y]))  -- Output: true
#eval is_bound "y" ((∀₀₀ "x" (atomic_L "P" [Lvar_x])) ∨₀ (atomic_L "Q" [Lvar_x, Lvar_y]))  -- Output: true

def ex_isBoundFormula := ∀₀₀ "x" (atomic_L "P" [Lvar_x, Lvar_z]) -- ∀x P(x, z)

#eval is_bound_list ["x", "z"] ex_isBoundFormula    -- Output: false (o z não é bound)
#eval is_bound_list ["x", "y"] ex_isBoundFormula    -- Output: true (ambas são bound)


-- -------------------------------------
-- TERM FREE FOR A VARIABLE IN A FORMULA
-- -------------------------------------

-- DEFINITION: Verifica if a term t is free for a variable x in a formula A
def is_free_for (t : LTerm) (x : String) : LFormula → Bool
| (atomic_L _ ts) =>
  Lfreevars t ∩ Lfreevars_formula (atomic_L "" ts) = ∅
| (¬₀ A) => is_free_for t x A
| (A ∨₀ B) => is_free_for t x A && is_free_for t x B
| (∀₀₀ y A) =>
  if x = y then
    Lfreevars t ∩ Lfreevars_formula (∀₀₀ y A) = ∅
  else
    is_free_for t x A

-- --------
-- Example:
-- --------

-- Example formulas: ∀x P(x) ∨ Q(x,y) and ∀x,y P(x) ∨ Q(x,y)
def ex_formula2 := (∀₀₀ "x" (atomic_L "P" [Lvar_x])) ∨₀ (atomic_L "Q" [Lvar_x, Lvar_y])
def ex_formula22 := (∀₀ {"x"} (atomic_L "P" [Lvar_x])) ∨₀ (atomic_L "Q" [Lvar_x, Lvar_y])
def ex_formula222 := (∀₀ {"x","y"} (atomic_L "P" [Lvar_x,Lvar_y])) ∨₀ (atomic_L "Q" [Lvar_x, Lvar_y])

-- Checks if term "y" is free for "x" in the example formulas
#eval is_free_for (Lvar_y) "x" ex_formula2                     -- Output: false
#eval is_free_for (Lvar_y) "x" ex_formula22                    -- Output: false
#eval is_free_for (Lvar_y) "x" ex_formula222                   -- Output: false
#eval is_free_for (Lvar_z) "x" (atomic_L "P" [Lvar_x, Lvar_y])   -- Output: true
#eval is_free_for (Lvar_y) "x" (atomic_L "P" [Lvar_x, Lvar_y])   -- Output: true



-- ----------------------------------------------------------------------
--                      "PRENEXIFICATION RULES"
-- ----------------------------------------------------------------------

/- Problema (14 ag) : Prenexification rules as axioms (keeps def and prim symbols)? Or as lemmas (does not keep)?
axiom L_DM_or (A B : LFormula) : (¬₀(A∨₀B)) = ((¬₀A)∧₀(¬₀B))
lemma L_DM_or (A B : LFormula) : (¬₀(A∨₀B)) = ((¬₀A)∧₀(¬₀B)) := by sorry
-/

-- DeMorgan laws
@[simp]
axiom L_prenex_DM_or (A B : LFormula) : (¬₀(A∨₀B)) = ((¬₀A)∧₀(¬₀B))
@[simp]
axiom L_prenex_DM_and (A B : LFormula) : (¬₀(A∧₀B)) = ((¬₀A)∨₀(¬₀B))

-- Negation
@[simp]
axiom L_prenex_neg_exists (A : LFormula) (x : String) : (¬₀(∃₀₀ x A)) = (∀₀₀ x (¬₀A))
@[simp]
axiom L_prenex_neg_forall (A : LFormula) (x : String) : (¬₀(∀₀₀ x A)) = (∃₀₀ x (¬₀A))

-- Conjunction
@[simp]
axiom L_prenex_forall_and (A B : LFormula) (x : String): ((∀₀₀ x A)∧₀B) = (∀₀₀ x (A∧₀B))     -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)
@[simp]
axiom L_prenex_exists_and (A B : LFormula) (x : String) : ((∃₀₀ x A)∧₀B) = (∃₀₀ x (A∧₀B))    -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)

-- Disjunction
@[simp]
axiom L_prenex_forall_or (A B : LFormula) (x : String) : ((∀₀₀ x A)∨₀B) = (∀₀₀ x (A∨₀B))     -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)
@[simp]
axiom L_prenex_exists_or (A B : LFormula) (x : String) : ((∃₀₀ x A)∨₀B) = (∃₀₀ x (A∨₀B))     -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)

-- Implication
@[simp]
axiom L_prenex_forall_imp (A B : LFormula) (x : String): ((∀₀₀ x A)→₀B) = (∃₀₀ x (A→₀B))     -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)
@[simp]
axiom L_prenex_exists_imp (A B : LFormula) (x : String) : ((∃₀₀ x A)→₀B) = (∀₀₀ x (A→₀B))    -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)

@[simp]
axiom L_prenex_imp_forall (A B : LFormula) (x : String): (A→₀(∀₀₀ x B)) = (∀₀₀ x (A→₀B))     -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)
@[simp]
axiom L_prenex_imp_exists (A B : LFormula) (x : String) : (A→₀(∃₀₀ x B)) = (∃₀₀ x (A→₀B))    -- TODO (14 ag) : (x ∈ (Lfreevars_formula A)) (x ∉ Lfreevars_formula B)

-- ------------------

-- Conjunction commutativity
@[simp]
axiom L_and_commut (A B : LFormula) : (A∧₀B) = (B∧₀A)

-- Disjunction commutativity
@[simp]
axiom L_or_commut (A B : LFormula) : (A∨₀B) = (B∨₀A)

-- ------------------

-- Double neg
@[simp]
axiom L_double_neg (A : LFormula) : (¬₀(¬₀A)) = A


-- --------------------------------------------------------------

inductive isAtomic_L : LFormula → Prop
| at_rel : isAtomic_L (atomic_L R lt)
