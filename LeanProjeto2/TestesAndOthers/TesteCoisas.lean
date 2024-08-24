import MathLib.Tactic

/- LISTAS
def tcha : 1 ∈ [1, 2, 3] := by simp
def tchu := [1,2,3]
#eval 1 ∈ tchu
-/


namespace Teste1

inductive Term
| var : String → Term
| pi : Term


inductive FormulaLevel
| atomic
| base
| unrestrictred
deriving Ord


def max  (f1 : FormulaLevel) (f2:FormulaLevel) : FormulaLevel  := if compare f1 f2 = Ordering.gt then f1 else f2


def ensure_base : FormulaLevel → FormulaLevel
| .atomic => .base
| x => x

inductive Formula : FormulaLevel → Type
| eq : Term → Term → Formula atomic
| belongs : Term → Term → Formula atomic

| neq : Formula b → Formula (ensure_base b)
| or : Formula b1 → Formula b2 → Formula (ensure_base (max b1 b2))


| forall : String → Formula b → Formula unrestricted


--open Formula

--example (f : Formula) (h:isAtomic f) : (isBase f) := by
--  apply?

end Teste1

-- ----------------------------------------
-- ----------------------------------------
-- ----------------------------------------
-- ----------------------------------------


namespace Teste2

inductive Term
| var : String → Term
| pi : Term
deriving Repr


inductive Formula
| eq : Term → Term → Formula
| belongs : Term → Term → Formula

| neg : Formula → Formula
| or : Formula → Formula → Formula


| forall : String → Formula → Formula

deriving Repr

open Formula

inductive isAtomic : Formula → Prop
| aeq: isAtomic (eq a b)
| abelongs: isAtomic (belongs a b)


inductive isBase : Formula → Prop
| batom :
  isAtomic f →
  -----------------
  isBase f
| bneg : isBase (neg f)
| bor : isBase (or f1  f2)




example (f: Formula) (h:isAtomic f)  : (isBase f) := by
  exact isBase.batom h

-- -----------------------------------------------

inductive NormalizesTo : Formula → Formula → Prop
| orLeft : NormalizesTo (or f1 f2) f1


def normal_form : Formula → Formula
| .or f1 f2 => f1
| .forall x f1 => f1
| x => x


def a : Term := .var "a"
def b : Term := .var "b"
def x : Term := .var "x"
def y : Term := .var "y"

def eq1 : Formula := .eq a b
def eq2 : Formula := .eq x y


#eval normal_form (.or eq1 eq2)


inductive Equivalent : Formula → Formula → Prop
| id : Equivalent A A
| comm : Equivalent A B → Equivalent B A
| nf_left : Equivalent A B → Equivalent (normal_form A) B
| nf_right : Equivalent A B → Equivalent A (normal_form B)


inductive isTrue : Formula → Prop
| lem : isTrue (.or A (.neg A))
| expansion:
  isTrue A →
  ------------
  isTrue (.or A B)
| equivalence :
  Equivalent A B →
  isTrue A →
  isTrue B



/-
-- Atomic formulas (maneira antiga de definir Atomic Formulas in L - FOL)

inductive LAtomic : Type
| atom : LPred → List LTerm → LAtomic
-/
end Teste2
