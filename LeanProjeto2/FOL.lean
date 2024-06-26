import LeanProjeto2

namespace FOL

-- Finite types [def 1.1]
inductive FTipe : Type
| ground : FTipe                 -- G
| arrow : FTipe → FTipe → FTipe  -- σ → τ
| star : FTipe → FTipe           -- σ*
