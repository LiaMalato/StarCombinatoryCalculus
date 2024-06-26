import LeanProjeto2
import MathLib.Tactic

namespace FOL

-- Finite types [def 1.1]
inductive FTipe : Type
| ground : FTipe                 -- G
| arrow : FTipe → FTipe → FTipe  -- σ → τ
| star : FTipe → FTipe           -- σ*


inductive P : Prop
| x
| y

lemma a (x:P) : P := by
  constructor
