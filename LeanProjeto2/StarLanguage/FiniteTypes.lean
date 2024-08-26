-- -------------------------------------------------------------
--            STAR LANGUAGE - FINITE TYPES
-- -------------------------------------------------------------

-- We import the definitions from the first-order language L:
import LeanProjeto2.FOLanguage
import MathLib.Tactic                   -- Pergunta: é preciso repetir isto?

open FOLang
open LFormula

-- ----------------------
-- FINITE TYPES
-- ----------------------

-- Finite types [def 1.1]
inductive FType : Type
| ground : FType                        -- G
| arrow : FType → FType → FType         -- σ → τ
| star : FType → FType                  -- σ*
deriving Repr, DecidableEq

open FType

-- Notation for finite types
def G := ground                         -- notation G => ground
notation t "⟶" t1 => arrow t t1
notation t "⋆" => star t

-- EXAMPLE:
def s1ex2_1 : FType := G⋆
def s1ex2_2 : FType := G ⟶ G
def s1ex2_3 : FType := G ⟶ (G ⟶ G)
def s1ex2_3' : FType := (G ⟶ G) ⟶ G
def s1ex2_4 : FType := (G ⟶ G) ⟶ (G ⟶ (G ⟶ G))
def s1ex2_5 (σ τ : FType) : FType := σ ⟶ ((σ⋆ ⟶ τ) ⟶ τ)
def s1ex2_5' (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆
example (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆

-- DEFINITION (Tuple of Types): We define tuples of types as lists
def FTypeTuple := List FType
deriving Repr, DecidableEq

-- EXAMPLE: two examples of tuples
def exTuple1 : FTypeTuple := [G]
def exTuple2 : FTypeTuple := [G⋆,G ⟶ G]
