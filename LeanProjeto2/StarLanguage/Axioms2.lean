-- -------------------------------------------------------------
--            STAR LANGUAGE - AXIOMS (new)
--          Versão adaptada de Patrick Massot
-- -------------------------------------------------------------

import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.Syntax
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Batteries
import MathLib.Tactic

open LFormula
open Term
open Formula
open Set
open Batteries

-- --------------------------------------
-- --------------------------------------
-- ------------- AXIOMS -----------------
-- --------------------------------------
-- --------------------------------------

namespace Axioms

/- ---------------------------------------------------------------
                  AXIOMS FOR VARIABLES (matrices)
-/ ---------------------------------------------------------------

def AxiomE1_matrix (x : String) : Formula :=
  (var x)=₁(var x)
def AxiomE2_matrix (x₁ x₂ : String) (A : Formula) (hA : isBase A) : Formula :=
  (((var x₁)=₁(var x₂)) ∧₁ A) →₁ (A.subst (HashMap.ofList ([x₁].zip ([x₂].tt))))
def AxiomUn_matrix (x : String) (t : String) (A : Formula) : Formula :=
  (b∀₁₁ x (var t) A) ↔₁ (∀₁₁ x (((var x) ∈₁ (var t)) →₁ A))
def AxiomC1_matrix (x₁ x₂ : String) : Formula :=
  ((Π₁·(var x₁))·(var x₂)) =₁ (var x₁)
--def AxiomC1_matrix (x₁ x₂ : String) : Formula := AxiomC1_matrix_ (.var x₁) (.var x₂)
def AxiomC2_matrix (x₁ x₂ x₃ : String) : Formula :=
  (((Σ₁·(var x₁))·(var x₂))·(var x₃)) =₁ (((var x₁)·(var x₃))·((var x₂)·(var x₃)))
def AxiomP1_matrix (x₁ x₂ : String) : Formula :=
  ((ind_⋃₁·(𝔰₁·(var x₁)))·(var x₂)) =₁ ((var x₂)·(var x₁))
def AxiomP2_matrix (x₁ x₂ x₃ : String) : Formula :=
  ((ind_⋃₁·((∪₁·(var x₁))·(var x₂)))·(var x₃)) =₁ ((∪₁·((ind_⋃₁·(var x₁))·(var x₃)))·((ind_⋃₁·(var x₂))·(var x₃)))
def AxiomS1_matrix (x₁ x₂ : String) : Formula :=
  ((var x₁) ∈₁ (𝔰₁·(var x₂))) ↔₁ ((var x₁) =₁ (var x₂))
def AxiomS2_matrix (x₁ x₂ x₃ : String) : Formula :=
  ((var x₁) ∈₁ ((∪₁·(var x₂))·(var x₃)) ) ↔₁ (((var x₁) ∈₁ (var x₂)) ∨₁ ((var x₁) ∈₁ (var x₃)))
def AxiomS3_matrix (x₁ x₂ x₃ y : String) : Formula :=
  ((var x₃) ∈₁ ((ind_⋃₁·(var x₁))·(var x₂))) ↔₁ (b∃₁₁ y (var x₁) ((var x₃) ∈₁ ((var x₂)·(var y))))
def AxiomS4_matrix (x₁ x₂ : String) : Formula :=
  b∃₁₁ x₂ (var x₁) ((var x₂) ∈₁ (var x₁))

/- ---------------------------------------------------------------
              CORRESPONDING AXIOMS FOR TERMS (matrices)
-/ ---------------------------------------------------------------

@[reducible, simp]
def AxiomE1_matrix_term (t : Term) : Formula :=
  t=₁t
@[reducible, simp]
def AxiomE2_matrix_term (x : String) (t : Term) (A : Formula) (hA : isBase A) : Formula :=
  (((var x)=₁t) ∧₁ A) →₁ (A.subst (HashMap.ofList ([x].zip ([t]))))
@[reducible, simp]
def AxiomUn_matrix_term (x : String) (t : Term) (A : Formula) : Formula :=
  (b∀₁₁ x t A) ↔₁ (∀₁₁ x (((var x) ∈₁ t) →₁ A))
@[reducible, simp]
def AxiomC1_matrix_term (t₁ t₂ : Term) : Formula :=
  ((Π₁·t₁)·t₂) =₁ t₁
@[reducible, simp]
def AxiomC2_matrix_term (t₁ t₂ t₃ : Term) : Formula :=
  (((Σ₁·t₁)·t₂)·t₃) =₁ ((t₁·t₃)·(t₂·t₃))
@[reducible, simp]
def AxiomP1_matrix_term (t₁ t₂ : Term) : Formula :=
  ((ind_⋃₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁)
@[reducible, simp]
def AxiomP2_matrix_term (t₁ t₂ t₃ : Term) : Formula :=
  ((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) =₁ ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃))
@[reducible, simp]
def AxiomS1_matrix_term (t₁ t₂ : Term) : Formula :=
  (t₁ ∈₁ (𝔰₁·t₂)) ↔₁ (t₁ =₁ t₂)
@[reducible, simp]
def AxiomS2_matrix_term (t₁ t₂ t₃ : Term) : Formula :=
  (t₁ ∈₁ ((∪₁·t₂)·t₃) ) ↔₁ ((t₁ ∈₁ t₂) ∨₁ (t₁ ∈₁ t₃))
@[reducible, simp]
def AxiomS3_matrix_term (t₁ t₂ t₃ : Term) (y : String) : Formula :=
  (t₃ ∈₁ ((ind_⋃₁·t₁)·t₂)) ↔₁ (b∃₁₁ y t₁ (t₃ ∈₁ (t₂·(var y))))
@[reducible, simp]
def AxiomS4_matrix_term (x : String) (t : Term) : Formula :=
  b∃₁₁ x t ((var x) ∈₁ t)


-- ------------------------------------------------------------------------
-- ------------------------------------------------------------------------

-- LEMMA: substituir não altera baseness
lemma Subst_isBase (A : Formula) (hA : isBase A) (x : List String) (t : List Term) : isBase (A.subst (HashMap.ofList (x.zip t))) := by
  cases hA
  . rename_i isAt_A
    sorry
  . rename_i A isB_A
    sorry
  . rename_i A B isB_A isB_B
    sorry
  . rename_i A x' t' isB_A
    sorry


/- ---------------------------------------------------------------
LEMAS: A maioria dos axiomas é universal closures de base formulas
-/ ---------------------------------------------------------------

open Formula
open isAtomic
open isBase

-- On AxiomE1:
lemma AxiomE1_univ_of_base (x:String) : (isBase (AxiomE1_matrix x)) := by
  unfold AxiomE1_matrix
  exact b_atom (isAtomic.at_eq (var x) (var x))

#check Axioms.AxiomE1_univ_of_base "x"

/-
#check SH_int2
def HHH {x₁ x₂ : String} {int_axC1 : Formula} : Prop := SH_int2 (axiomC1_matrix x₁ x₂) int_axC1
--#check axiomE1_matrix
def HHHH := (axiomE1_matrix "x").components2
#eval (axiomE1_matrix "x").components2

def HHH : Prop := SH_int2 (axiomC1_matrix x₁ x₂) int_axC1
example
  (hInt : SH_int2 (axiomC1_matrix x₁ x₂) int_axC1)
  (hComp : (a,b,mat_axC1) = int_axC1.components2) :
  (a = ∅) ∧ (b = ∅) := by sorry
-/


-- On AxiomE2:
lemma AxiomE2_univ_of_base : (isBase (AxiomE2_matrix x₁ x₂ A hA)) := by
  unfold AxiomE2_matrix
  have H1 := Subst_isBase A hA [x₁] [x₂].tt
  have H2 := b_atom (isAtomic.at_eq (var x₁) (var x₂))
  have H3 := Conj_base ((var x₁)=₁(var x₂)) A H2 hA
  exact Imp_base ((var x₁=₁var x₂)∧₁A) (A.subst (HashMap.ofList ([x₁].zip [x₂].tt))) H3 H1


-- COMMENT: AxiomUn_univ_of_base não dá porque axiomUn não é base :)

lemma AxiomC1_univ_of_base : (isBase (AxiomC1_matrix x₁ x₂)) := by
  unfold AxiomC1_matrix
  exact b_atom (isAtomic.at_eq ((Π₁·var x₁)·var x₂) (var x₁))

lemma AxiomC2_univ_of_base : (isBase (AxiomC2_matrix x₁ x₂ x₃)) := by
  unfold AxiomC2_matrix
  exact b_atom (isAtomic.at_eq (((Σ₁·(var x₁))·(var x₂))·(var x₃)) (((var x₁)·(var x₃))·((var x₂)·(var x₃))))

lemma AxiomP1_univ_of_base : (isBase (AxiomP1_matrix x₁ x₂)) := by
  unfold AxiomP1_matrix
  exact b_atom (isAtomic.at_eq ((ind_⋃₁·(𝔰₁·(var x₁)))·(var x₂)) ((var x₂)·(var x₁)))

lemma AxiomP2_univ_of_base : (isBase (AxiomP2_matrix x₁ x₂ x₃)) := by
  unfold AxiomP2_matrix
  exact b_atom (isAtomic.at_eq ((ind_⋃₁·((∪₁·(var x₁))·(var x₂)))·(var x₃)) ((∪₁·((ind_⋃₁·(var x₁))·(var x₃)))·((ind_⋃₁·(var x₂))·(var x₃))))

lemma AxiomS1_univ_of_base : (isBase (AxiomS1_matrix x₁ x₂)) := by
  unfold AxiomS1_matrix
  have H1 := b_atom (isAtomic.at_mem (var x₁) (𝔰₁·(var x₂)))
  have H2 := b_atom (isAtomic.at_eq (var x₁) (var x₂))
  exact Iff_base (var x₁∈₁𝔰₁·var x₂) (var x₁=₁var x₂) H1 H2

lemma AxiomS2_univ_of_base : (isBase (AxiomS2_matrix x₁ x₂ x₃)) := by
  unfold AxiomS2_matrix
  have H1 := b_atom (isAtomic.at_mem (var x₁) ((∪₁·(var x₂))·(var x₃)))
  have H2 := b_atom (isAtomic.at_mem (var x₁) (var x₂))
  have H3 := b_atom (isAtomic.at_mem (var x₁) (var x₃))
  have H4 := b_or H2 H3
  exact Iff_base (var x₁∈₁(∪₁·var x₂)·var x₃) ((var x₁∈₁var x₂).or (var x₁∈₁var x₃)) H1 H4

lemma AxiomS3_univ_of_base {x₁ x₂ x₃ y : String} : (isBase (AxiomS3_matrix x₁ x₂ x₃ y)) := by
  unfold AxiomS3_matrix
  have H1 := b_atom (isAtomic.at_mem (var x₃) ((ind_⋃₁·(var x₁))·(var x₂)))
  have H2 := b_atom (isAtomic.at_mem (var x₃) ((var x₂)·(var y)))
  have H3 := bExists_base y (var x₁) H2
  exact Iff_base (var x₃ ∈₁(ind_⋃₁·var x₁)·var x₂) (b∃₁₁ y (var x₁) (var x₃∈₁var x₂·var y)) H1 H3

lemma AxiomS4_univ_of_base : (isBase (AxiomS4_matrix x₁ x₂)) := by
  unfold AxiomS4_matrix
  have H := b_atom (isAtomic.at_mem (var x₂) (var x₁))
  exact bExists_base x₂ (var x₁) H

-- ---------------------------------------------------------------

/- ---------------------------------------------------------------
      UNIVERSAL CLOSURE OF THE MATRICES FROM BEFORE (variables)
-/ ---------------------------------------------------------------

def AxiomE1 (x : String) : Formula :=
  ∀₁₁ x (AxiomE1_matrix x)
def AxiomE2 (x₁ x₂ : String) (A : Formula) (hA : isBase A) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (AxiomE2_matrix x₁ x₂ A hA))
def AxiomUn (x : String) (t : String) (A : Formula) : Formula :=
  ∀₁₁ t (AxiomUn_matrix x t A)
def AxiomC1 (x₁ x₂ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (AxiomC1_matrix x₁ x₂))
def AxiomC2 (x₁ x₂ x₃ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (∀₁₁ x₃ (AxiomC2_matrix x₁ x₂ x₃)))
def AxiomP1 (x₁ x₂ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (AxiomP1_matrix x₁ x₂))
def AxiomP2 (x₁ x₂ x₃ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (∀₁₁ x₃ (AxiomP2_matrix x₁ x₂ x₃)))
def AxiomS1 (x₁ x₂ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (AxiomS1_matrix x₁ x₂))
def AxiomS2 (x₁ x₂ x₃ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (∀₁₁ x₃ (AxiomS2_matrix x₁ x₂ x₃)))
def AxiomS3 (x₁ x₂ x₃ y : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (∀₁₁ x₃ (AxiomS3_matrix x₁ x₂ x₃ y)))
def AxiomS4 (x₁ x₂ : String) : Formula :=
  ∀₁₁ x₁ (AxiomS4_matrix x₁ x₂)

-- ---------------------------------------------------------------

-- Versão mega completa mas com [] o que é chato para as provas
def BAxiomE1 (x : String) : Formula :=
  ∀₁ [x]                ((var x)=₁(var x))
def BAxiomE11 (x : String) : Formula :=
  ∀₁₁ x                 ((var x)=₁(var x))
def BAxiomE2 (x₁ x₂ : String) (A : Formula) (hA : isBase A) : Formula :=
  ∀₁ [x₁,x₂]            ((var x₁)=₁(var x₂)) ∧₁ (A →₁ (A.subst (HashMap.ofList ([x₁].zip ([x₂].tt)))))
def BAxiomUn (x : String) (t : String) (A : Formula) : Formula :=
  ∀₁ [t]                (b∀₁₁ x (var t) A) ↔₁ (∀₁₁ x (((var x) ∈₁ (var t)) →₁ A))
def BAxiomC1 (x₁ x₂ : String) : Formula :=
  ∀₁ [x₁,x₂]            (((Π₁·(var x₁))·(var x₂)) =₁ (var x₁))
def BAxiomC2 (x₁ x₂ x₃ : String) : Formula :=
  ∀₁ [x₁, x₂, x₃]       ((((Σ₁·(var x₁))·(var x₂))·(var x₃)) =₁ (((var x₁)·(var x₃))·((var x₂)·(var x₃))))
def BAxiomP1 (x₁ x₂ : String) : Formula :=
  ∀₁ [x₁,x₂]            (((ind_⋃₁·(𝔰₁·(var x₁)))·(var x₂)) =₁ ((var x₂)·(var x₁)))
def BAxiomP2 (x₁ x₂ x₃ : String) : Formula :=
  ∀₁ [x₁, x₂, x₃]       (((ind_⋃₁·((∪₁·(var x₁))·(var x₂)))·(var x₃)) =₁ ((∪₁·((ind_⋃₁·(var x₁))·(var x₃)))·((ind_⋃₁·(var x₂))·(var x₃))))
def BAxiomS1 (x₁ x₂ : String) : Formula :=
  ∀₁ [x₁,x₂]            (((var x₁) ∈₁ (𝔰₁·(var x₂))) ↔₁ ((var x₁) =₁ (var x₂)))
def BAxiomS2 (x₁ x₂ x₃ : String) : Formula :=
  ∀₁ [x₁, x₂, x₃]       ((var x₁) ∈₁ ((∪₁·(var x₂))·(var x₃)) ) ↔₁ (((var x₁) ∈₁ (var x₂)) ∨₁ ((var x₁) ∈₁ (var x₃)))
def BAxiomS3 (x₁ x₂ x₃ y : String) : Formula :=
  ∀₁ [x₁, x₂, x₃]       (((var x₃) ∈₁ ((ind_⋃₁·(var x₁))·(var x₂))) ↔₁ (b∃₁₁ y (var x₁) ((var x₃) ∈₁ ((var x₂)·(var y)))))
def BAxiomS4 (x₁ x₂ : String) : Formula :=
  ∀₁ [x₁]               (b∃₁₁ x₂ (var x₁) ((var x₂) ∈₁ (var x₁)))

end Axioms

--def Axreflexivity (x : String) : Formula := (Term.var x) =₁ (Term.var x)

-- ---------------------------------------------------------------



/- ---------------------------------------------------------------
DEFINITION: 'ProvableFrom' - axiomas e regras de inferência
-/ ---------------------------------------------------------------

section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` is the predicate that there is a proof tree with conclusion `A` with assumptions from `Γ`.
This is a typical list of rules for natural deduction with classical logic. -/

open Axioms

inductive ProvableFrom : Set Formula → Formula → Prop
| ax    : ∀ {Γ A},            A ∈ Γ             → Γ ⊢ A

-- TWO AXIOM SCHEMA:
| exMid : ∀ {A},              Γ ⊢ ((¬₁A)∨₁A)
| subs : ∀ {A},               Γ ⊢ ((∀₁ x A) →₁ (A.subst (HashMap.ofList (x.zip t))))

-- FIVE RULES:
| exp :     ∀ {A B},          Γ ⊢ A             →   Γ ⊢ (B∨₁A)
| contrad : ∀ {A},            Γ ⊢ (A∨₁A)        →   Γ ⊢ A
| assoc :   ∀ {A B C},        Γ ⊢ (A∨₁(B∨₁C))   →   Γ ⊢ ((A∨₁B)∨₁C)
| cut :     ∀ {A B C},        Γ ⊢ (A∨₁B)        →   Γ ⊢ ((¬₁A)∨₁C)      →   Γ ⊢ (B∨₁C)
| forallInt : ∀ {A B},        Γ ⊢ (A∨₁B)        →   Γ ⊢ ((∀₁ x A)∨₁B)   -- TBD: falta x does not occur free in B

-- AXIOMS:
| AxE₁:                       Γ ⊢ AxiomE1 x
| AxE₂:                       Γ ⊢ AxiomE2 x₁ x₂ A hA
| AxU:                        Γ ⊢ AxiomUn x t A
| AxC₁:                       Γ ⊢ AxiomC1 x₁ x₂
| AxC₂:                       Γ ⊢ AxiomC2 x₁ x₂ x₃
| AxP₁:                       Γ ⊢ AxiomP1 x₁ x₂
| AxP₂:                       Γ ⊢ AxiomP2 x₁ x₂ x₃
| AxS₁:                       Γ ⊢ AxiomS1 x₁ x₂
| AxS₂:                       Γ ⊢ AxiomS2 x₁ x₂ x₃
| AxS₃:                       Γ ⊢ AxiomS3 x₁ x₂ x₃ y
| AxS₄:                       Γ ⊢ AxiomS4 x₁ x₂


/-
| AxE₁_term (t:Term) :                               Γ ⊢ (t=₁t)
| AxE₂_term (t₁ t₂ :Term) (hA : isBase A) :          Γ ⊢ ((t₁=₁t₂) ∧₁ (A →₁ A))     -- TBD: falta substituição aqui
| AxU_term (x : String) (t : Term) (A : Formula) :   Γ ⊢ ((b∀₁₁ x t A) ↔₁ (∀₁₁ x (((var x) ∈₁ t) →₁ A)))
| AxC₁_term (t₁ t₂ : Term) :                         Γ ⊢ (((Π₁·t₁)·t₂) =₁ t₁)
| AxC₂_term (t₁ t₂ t₃ : Term) :                      Γ ⊢ ((((Σ₁·t₁)·t₂)·t₃) =₁ ((t₁·t₃)·(t₂·t₃)))
| AxP₁_term (t₁ t₂ : Term) :                         Γ ⊢ (((ind_⋃₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁))
| AxP₂_term (t₁ t₂ t₃ : Term) :                      Γ ⊢ (((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) =₁ ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)))
| AxS₁_term (t₁ t₂ : Term) :                         Γ ⊢ ((t₁ ∈₁ (𝔰₁·t₂)) ↔₁ (t₁ =₁ t₂))
| AxS₂_term (t₁ t₂ t₃ : Term) :                      Γ ⊢ ((t₁ ∈₁ ((∪₁·t₂)·t₃) ) ↔₁ ((t₁ ∈₁ t₂) ∨₁ (t₁ ∈₁ t₃)))
| AxS₃_term (a f b : Term) :                         Γ ⊢ ((b ∈₁ ((ind_⋃₁·a)·f)) ↔₁ (b∃₁₁ x a (b ∈₁ (f·(var x)))))
-- TBD: FALTA AXS4
-/

axiom AxE₁_term (Γ : Set Formula) (t:Term): Γ ⊢ (t=₁t)
axiom AxE₂_term (Γ : Set Formula) (x x₁:String) (t :Term) (A:Formula) (hA : isBase A) :       Γ ⊢ (((var x₁)=₁t) ∧₁ (A →₁ (A.subst (HashMap.ofList ([x].zip [t])))))
axiom AxU_term (Γ : Set Formula) (x : String) (t : Term) (A : Formula) :                      Γ ⊢ ((b∀₁₁ x t A) ↔₁ (∀₁₁ x (((var x) ∈₁ t) →₁ A)))
axiom AxC₁_term (Γ : Set Formula) (t₁ t₂ : Term) :                                            Γ ⊢ (((Π₁·t₁)·t₂) =₁ t₁)
axiom AxC₂_term (Γ : Set Formula) (t₁ t₂ t₃ : Term) :                                         Γ ⊢ ((((Σ₁·t₁)·t₂)·t₃) =₁ ((t₁·t₃)·(t₂·t₃)))
axiom AxP₁_term (Γ : Set Formula) (t₁ t₂ : Term) :                                            Γ ⊢ (((ind_⋃₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁))
axiom AxP₂_term (Γ : Set Formula) (t₁ t₂ t₃ : Term) :                                         Γ ⊢ (((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) =₁ ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)))
axiom AxS₁_term (Γ : Set Formula) (t₁ t₂ : Term) :                                            Γ ⊢ ((t₁ ∈₁ (𝔰₁·t₂)) ↔₁ (t₁ =₁ t₂))
axiom AxS₂_term (Γ : Set Formula) (t₁ t₂ t₃ : Term) :                                         Γ ⊢ ((t₁ ∈₁ ((∪₁·t₂)·t₃) ) ↔₁ ((t₁ ∈₁ t₂) ∨₁ (t₁ ∈₁ t₃)))
axiom AxS₃_term (Γ : Set Formula) (x:String) (a f b : Term) :                                 Γ ⊢ ((b ∈₁ ((ind_⋃₁·a)·f)) ↔₁ (b∃₁₁ x a (b ∈₁ (f·(var x)))))
-- TBD: FALTA AXS4


end

def bAC2 (x y f : String) (A : Formula) : Formula :=
  ((∀₁₁ x (∃₁₁ y A)) →₁ (∃₁₁ f (∀₁₁ x (b∃₁₁ y ((var f)·(var x)) A))))     -- bAC^ω_*  (a tirar)
def bAC_star_om (x y f a b : String) (A : Formula) : Formula :=
  ((∀₁₁ x (∃₁₁ y A)) →₁ (∃₁₁ f (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A))))     -- bAC^ω_*  (a tirar)
def bAC (x y f a b : List String) (A : Formula) : Formula :=
  ((∀₁ x (∃₁ y A)) →₁ (∃₁ f (∀₁ a (b∃₁ b ((f.tt)⊙(a.tt)) A))))     -- bAC^ω_*


infix:27 (priority := high) " ⊢ " => ProvableFrom     -- já não é a mesma notação que em ProvableFrom!

/- A formula is provable if there is a -/
/-
This definition states that a formula A is considered provable
if it can be derived (or proved) from an empty set of assumptions.
In other words, Provable A holds true if A can be proved purely
by the logical rules defined in the ProvableFrom inductive type,
without relying on any specific assumptions.
-/
-- DEF: A formula is said to be provable if it can be derived using ProvableFrom and nothing else
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax exMid subs exp contrad assoc cut forallInt AxE₁ AxE₂ AxU AxC₁ AxC₂ AxP₁ AxP₂ AxS₁ AxS₂ AxS₃ AxS₄)
variable {Γ Δ : Set Formula}

/- We define a simple tactic `apply_ax` to prove something using the `ax` rule. -/
syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_insert | apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

/-
se não teriamos de usar os seguintes lemas about insert:
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
-/


-- Define the reflexivity proof for terms
/-
theorem term_reflexivity {t:Term}: ∅ ⊢ (t =₁ t) :=
  match t with
  | var x => by refine ProvableFrom.contrad ?_
  | Term.lcons l => by simp
  | Term.app t1 t2 => by simp [term_reflexivity t1, term_reflexivity t2]
-/

--example (A : Formula) {f : List String} : (insert (bAC x y f B) ∅ ⊢ A) → (Provable A) := by sorry
--theorem Soundness (A : Formula) {f : String} : (insert (bAC x y f B) ∅ ⊢ A) → (∃(t: List Term), (Provable (∀₁ a A))) := by sorry    -- TBD: falta subst aqui
--theorem Characterization (A : Formula) {f : String} : (insert (bAC x y f B) ∅ ⊢ A) → (Provable (A ∨₁ A)) := by sorry          -- TBD: falta A^SH aqui
--lemma Lem32 (A : Formula) (hA : isBase A) {f : String}: (insert (bAC x y f B) ∅ ⊢ ((b∀₁ x t (∃₁ y A)) →₁ (∃₁₁ b (b∀₁ x t (b∃₁ y (b.tt) A))))) := by sorry




/-
example : insert A (insert B ∅) ⊢ A ∧₁ B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_insert _ _)))

example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (by apply_ax) (by apply_ax)
-/


-- OUTRAS COISAS IMPORTANTES (ex de FOL)

@[simp] axiom DoubleNeg (A:Formula) : ((¬₁(¬₁ A)) = A)
@[simp] axiom DeMorgan_or (A B : Formula) : ((¬₁(A∨₁B)) = (¬₁A)∧₁(¬₁B))
@[simp] axiom DeMorgan_and (A B : Formula) : ((¬₁(A∧₁B)) = (¬₁A)∨₁(¬₁B))

-- EXAMPLES
example (A : Formula) : (¬₁(¬₁(¬₁A))) = (¬₁ A) :=
by
  simp
  --exact DoubleNeg A.not   OR     apply (DoubleNeg A.not)

example (A : Formula) : (¬₁(¬₁A)) = A :=
by
  exact DoubleNeg A
