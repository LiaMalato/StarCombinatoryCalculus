import MathLib.Tactic

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


open Formula




--example (f : Formula) (h:isAtomic f) : (isBase f) := by
--  apply?
