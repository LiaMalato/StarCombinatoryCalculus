import MathLib.Tactic

-- -------------------------------------------------------------
-- -------------------------------------------------------------
--             STAR LANGUAGE - FINITE TYPES
--             (SECTION 1.1: Finite types)
-- -------------------------------------------------------------
-- -------------------------------------------------------------

/- FILE DESCRIPTION:
In this file we present the definition for finite types together
with some examples. The file corresponds to pages 5 to 8.
-/

-- -------------------------------------------------------------
-- DEFINITION 1.1 (p.5):
-- Finite types
-- -------------------------------------------------------------

-- Definition of finite types
inductive FType
| ground :  FType                        -- the ground type G
| arrow :   FType → FType → FType        -- the function type σ → τ
| star :    FType → FType                -- the star type σ*
deriving Repr, DecidableEq

open FType

-- Notation for finite types
def G := ground
notation σ "⟶" τ => arrow σ τ
notation σ "⋆" => star σ

-- -------------------------------------------------------------
-- EXAMPLE 1.2 (p.6):
-- Examples of finite types
-- -------------------------------------------------------------

-- Example:
def s1ex2_1 : FType                := G⋆
def s1ex2_2 : FType                := G ⟶ G
def s1ex2_3 : FType                := G ⟶ (G ⟶ G)
def s1ex2_3' : FType               := (G ⟶ G) ⟶ G
def s1ex2_4 : FType                := (G ⟶ G) ⟶ (G ⟶ (G ⟶ G))
def s1ex2_5 (σ τ : FType) : FType  := σ ⟶ ((σ⋆ ⟶ τ) ⟶ τ)
def s1ex2_5' (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆
example (σ τ : FType) : FType      := (σ⋆ ⟶ τ)⋆
