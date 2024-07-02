import LeanProjeto2
import MathLib.Tactic
import Init.Data.String.Basic
-- import data.string.basic

namespace FOL

-- --------------------
-- CONSTANTES
-- --------------------

-- Variáveis

def LVar : Type := String

-- Logical connectives (∨ , ¬)

inductive LogCon : Type
| Ldisj
| Lnot
| Lforall

open LogCon

-- --------------------
-- TERMOS
-- --------------------

inductive LTerm : Type
| Lvar : LVar → LTerm
| Lconst : String → LTerm
| Lfunc : String → List LTerm → LTerm

-- Predicate symbols
def LPred : Type := String

-- --------------------
-- FORMULAS
-- --------------------

-- Atomic formulas

inductive LAtomic : Type
| atom : LPred → List LTerm → LAtomic

-- Formulas
inductive LFormula : Type     -- VARIAVEIS
| atomic_L : LAtomic → LFormula               -- Atomic formulas
| not_L : LFormula → LFormula                -- Negation
| or_L : LFormula → LFormula → LFormula      -- Disjunction
| forall_L : LVar → LFormula → LFormula      -- Universal quantification

open LFormula

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
  not_L (forall_L x (not_L A))

notation A "↔₀" B => iff_L A B
notation "∃₀" x A => exists_L x A

-- ∃x A := ¬ (∀x (¬ A))                                -- NOT WORKING
def lexists (x : LVar) (φ : LFormula) : LFormula :=
  ¬₀ (∀₀ x (¬₀ φ))
