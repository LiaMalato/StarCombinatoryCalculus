-- -------------------------------------------------------------
--            STAR LANGUAGE - FINITE TYPES
-- -------------------------------------------------------------

import MathLib.Tactic

-- ----------------------
-- FINITE TYPES
-- ----------------------

-- Finite types [def 1.1]
inductive FType
| ground : FType                        -- G
| arrow : FType → FType → FType         -- σ → τ
| star : FType → FType                  -- σ*
deriving Repr, DecidableEq

open FType

-- Notation for finite types
def G := ground                         -- notation G => ground
notation σ "⟶" τ => arrow σ τ
notation σ "⋆" => star σ

def exCreateType (σ τ : FType) : FType := (σ⋆) ⟶ τ

-- (G⋆) ⟶ (G ⟶ G)

-- EXAMPLE:
def s1ex2_1 : FType := G⋆
def s1ex2_2 : FType := G ⟶ G
def s1ex2_3 : FType := G ⟶ (G ⟶ G)
def s1ex2_3' : FType := (G ⟶ G) ⟶ G
def s1ex2_4 : FType := (G ⟶ G) ⟶ (G ⟶ (G ⟶ G))
def s1ex2_5 (σ τ : FType) : FType := σ ⟶ ((σ⋆ ⟶ τ) ⟶ τ)
def s1ex2_5' (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆
example (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆


-- ----------------------
-- TYPE TUPLES
-- ----------------------

/-
Type tuples can easily be implemented as lists of finite types (List FType)
-/

-- EXAMPLE: two type tuples
def exTuple1 : List FType := [G]
def exTuple2 : List FType := [G⋆,G ⟶ G]


-- ESTA MAL
-- DEFINITION (arrow constructor between two type tuples):
def arrowTuples : List FType → List FType → FType
| [], τ => match τ with
  | []      => G  -- base case: if both lists are empty, return the ground type
  | t::ts   => t  -- if σ is empty, the result is just the list τ's first element
| σ, [] => G  -- if τ is empty, we return the ground type
| σ, t::ts => (σ.foldr arrow t) ⟶ arrowTuples σ ts


notation σₜ "⟿" τₜ => arrowTuples σₜ τₜ





--def FTypeTuple := List FType
--deriving Repr, DecidableEq
