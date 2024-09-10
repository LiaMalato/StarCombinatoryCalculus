-- -------------------------------------------------------------
--       STAR LANGUAGE - RESULTS and OTHER DEFINITIONS
-- -------------------------------------------------------------

import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.Axioms2
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.FiniteTypes
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Batteries

open LFormula
open Term
open Formula
open Set
open Batteries

/-
#check 5
#check 5+3

def AddThree (n:ℕ) : ℕ := n+3
#eval AddThree 5

lemma AddResult (m n l : ℕ) : m+(n+l) = l+(n+m) :=
  by
    rw [← add_assoc m n l]
    rw [add_comm (m+n) l]
    rw [add_comm m n]

lemma AddResult2 (m n l : ℕ) : m+(n+l) = l+(n+m) :=
  by
    linarith
-/
