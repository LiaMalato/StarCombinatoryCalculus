import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.Syntax
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Batteries

open Term
open Formula
open Set
open Batteries

-- -------------------------------------------------------------
-- -------------------------------------------------------------
--                   STAR LANGUAGE - AXIOMS
--        (SECTION 1.2.2: The axiomatic)
--        (SECTION 1.2.3: The Bounded Axiom of Choice)
-- -------------------------------------------------------------
-- -------------------------------------------------------------

/- FILE DESCRIPTION:
In this file we discuss the axiomatic and the Bounded Axiom of
Choice. The file corresponds to pages 14 to 18.
-/

namespace axioms

/- ---------------------------------------------------------------
                  AXIOMS FOR VARIABLES (matrices)
-/ ---------------------------------------------------------------

-- The matrices of the axioms

def AxiomE1_matrix (x : String) : Formula :=
  (var x)=₁(var x)
def AxiomE2_matrix (x₁ x₂ : String) (A : Formula) (hA : isBase A) : Formula :=
  (((var x₁)=₁(var x₂)) ∧₁ A) →₁ (A.subst (HashMap.ofList ([x₁].zip ([x₂].tt))))
def AxiomUn_matrix (x : String) (t : String) (A : Formula) : Formula :=
  (b∀₁₁ x (var t) A) ↔₁ (∀₁₁ x (((var x) ∈₁ (var t)) →₁ A))
def AxiomC1_matrix (x₁ x₂ : String) : Formula :=      -- The matrix of Axiom AxC1
  ((Π₁·(var x₁))·(var x₂)) =₁ (var x₁)                -- Given variables x₁ x₂: (Π·x₁)·x₂ = x₁
def AxiomC2_matrix (x₁ x₂ x₃ : String) : Formula :=
  (((Σ₁·(var x₁))·(var x₂))·(var x₃)) =₁ (((var x₁)·(var x₃))·((var x₂)·(var x₃)))
def AxiomP1_matrix (x₁ x₂ : String) : Formula :=
  ((i∪₁·(𝔰₁·(var x₁)))·(var x₂)) =₁ ((var x₂)·(var x₁))
def AxiomP2_matrix (x₁ x₂ x₃ : String) : Formula :=
  ((i∪₁·((∪₁·(var x₁))·(var x₂)))·(var x₃)) =₁ ((∪₁·((i∪₁·(var x₁))·(var x₃)))·((i∪₁·(var x₂))·(var x₃)))
def AxiomS1_matrix (x₁ x₂ : String) : Formula :=
  ((var x₁) ∈₁ (𝔰₁·(var x₂))) ↔₁ ((var x₁) =₁ (var x₂))
def AxiomS2_matrix (x₁ x₂ x₃ : String) : Formula :=
  ((var x₁) ∈₁ ((∪₁·(var x₂))·(var x₃)) ) ↔₁ (((var x₁) ∈₁ (var x₂)) ∨₁ ((var x₁) ∈₁ (var x₃)))
def AxiomS3_matrix (x₁ x₂ x₃ y : String) : Formula :=
  ((var x₃) ∈₁ ((i∪₁·(var x₁))·(var x₂))) ↔₁ (b∃₁₁ y (var x₁) ((var x₃) ∈₁ ((var x₂)·(var y))))
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
  ((i∪₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁)
@[reducible, simp]
def AxiomP2_matrix_term (t₁ t₂ t₃ : Term) : Formula :=
  ((i∪₁·((∪₁·t₁)·t₂))·t₃) =₁ ((∪₁·((i∪₁·t₁)·t₃))·((i∪₁·t₂)·t₃))
@[reducible, simp]
def AxiomS1_matrix_term (t₁ t₂ : Term) : Formula :=
  (t₁ ∈₁ (𝔰₁·t₂)) ↔₁ (t₁ =₁ t₂)
@[reducible, simp]
def AxiomS2_matrix_term (t₁ t₂ t₃ : Term) : Formula :=
  (t₁ ∈₁ ((∪₁·t₂)·t₃) ) ↔₁ ((t₁ ∈₁ t₂) ∨₁ (t₁ ∈₁ t₃))
@[reducible, simp]
def AxiomS3_matrix_term (t₁ t₂ t₃ : Term) (y : String) : Formula :=
  (t₃ ∈₁ ((i∪₁·t₁)·t₂)) ↔₁ (b∃₁₁ y t₁ (t₃ ∈₁ (t₂·(var y))))
@[reducible, simp]
def AxiomS4_matrix_term (x : String) (t : Term) : Formula :=
  b∃₁₁ x t ((var x) ∈₁ t)

-- "Axioms" for term tuples
def AxiomS1_term_tuple (t₁ t₂ : List Term) : Formula :=
  (t₁ ∈_t ([𝔰₁] ⊙ t₂)) ↔₁ (t₁ =_t t₂)


/- ---------------------------------------------------------------
                      AUXILLIARY LEMMAS
-/ ---------------------------------------------------------------

open Formula
open isAtomic
open isBase

-- AUXILLIARY LEMMA: substitution does not affect baseness
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

-- LEMMAS: Most axioms are universal closures of base formulas
lemma AxiomE1_univ_of_base (x:String) : (isBase (AxiomE1_matrix x)) := by
  unfold AxiomE1_matrix
  exact b_atom (isAtomic.at_eq (var x) (var x))

#check axioms.AxiomE1_univ_of_base "x"

lemma AxiomE2_univ_of_base : (isBase (AxiomE2_matrix x₁ x₂ A hA)) := by
  unfold AxiomE2_matrix
  have H1 := Subst_isBase A hA [x₁] [x₂].tt
  have H2 := b_atom (isAtomic.at_eq (var x₁) (var x₂))
  have H3 := Conj_base ((var x₁)=₁(var x₂)) A H2 hA
  exact Imp_base ((var x₁=₁var x₂)∧₁A) (A.subst (HashMap.ofList ([x₁].zip [x₂].tt))) H3 H1

lemma AxiomC1_univ_of_base : (isBase (AxiomC1_matrix x₁ x₂)) := by
  unfold AxiomC1_matrix
  exact b_atom (isAtomic.at_eq ((Π₁·var x₁)·var x₂) (var x₁))

lemma AxiomC2_univ_of_base : (isBase (AxiomC2_matrix x₁ x₂ x₃)) := by
  unfold AxiomC2_matrix
  exact b_atom (isAtomic.at_eq (((Σ₁·(var x₁))·(var x₂))·(var x₃)) (((var x₁)·(var x₃))·((var x₂)·(var x₃))))

lemma AxiomP1_univ_of_base : (isBase (AxiomP1_matrix x₁ x₂)) := by
  unfold AxiomP1_matrix
  exact b_atom (isAtomic.at_eq ((i∪₁·(𝔰₁·(var x₁)))·(var x₂)) ((var x₂)·(var x₁)))

lemma AxiomP2_univ_of_base : (isBase (AxiomP2_matrix x₁ x₂ x₃)) := by
  unfold AxiomP2_matrix
  exact b_atom (isAtomic.at_eq ((i∪₁·((∪₁·(var x₁))·(var x₂)))·(var x₃)) ((∪₁·((i∪₁·(var x₁))·(var x₃)))·((i∪₁·(var x₂))·(var x₃))))

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
  have H1 := b_atom (isAtomic.at_mem (var x₃) ((i∪₁·(var x₁))·(var x₂)))
  have H2 := b_atom (isAtomic.at_mem (var x₃) ((var x₂)·(var y)))
  have H3 := bExists_base y (var x₁) H2
  exact Iff_base (var x₃ ∈₁(i∪₁·var x₁)·var x₂) (b∃₁₁ y (var x₁) (var x₃∈₁var x₂·var y)) H1 H3

lemma AxiomS4_univ_of_base : (isBase (AxiomS4_matrix x₁ x₂)) := by
  unfold AxiomS4_matrix
  have H := b_atom (isAtomic.at_mem (var x₂) (var x₁))
  exact bExists_base x₂ (var x₁) H

/- ---------------------------------------------------------------
      UNIVERSAL CLOSURE OF THE MATRICES FROM BEFORE (variables)
-/ ---------------------------------------------------------------

-- Universal closures

def AxiomE1 (x : String) : Formula :=
  ∀₁₁ x (AxiomE1_matrix x)
def AxiomE2 (x₁ x₂ : String) (A : Formula) (hA : isBase A) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (AxiomE2_matrix x₁ x₂ A hA))
def AxiomUn (x : String) (t : String) (A : Formula) : Formula :=
  ∀₁₁ t (AxiomUn_matrix x t A)
def AxiomC1 (x₁ x₂ : String) : Formula :=       -- AxC₁ as the universal closure of (Π·x₁)·x₂ = x₁
  ∀₁₁ x₁ (∀₁₁ x₂ (AxiomC1_matrix x₁ x₂))        -- Given variables x₁ x₂: ∀x₁,x₂[(Π·x₁)·x₂ = x₁]
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

end axioms


/- ---------------------------------------------------------------
                          THE AXIOMATIC
-/ ---------------------------------------------------------------

/-
We define 'ProvableFrom' to describe the axiomatic with the axiom
schema, the inference rules and the previous axioms.
-/

section
set_option hygiene false
local infix:27 " ⊢ " => ProvableFrom

/-
Writing 'Γ ⊢ A' states that from the assumptions from 'Γ' we can
conclude 'A'.
-/

open axioms

inductive ProvableFrom : Set Formula → Formula → Prop

-- 1. TWO AXIOM SCHEMA:
| exMid : ∀ {A},              Γ ⊢ ((¬₁A)∨₁A)
| subs : ∀ {A},               Γ ⊢ ((∀₁₁ x A) →₁ (A.subst (HashMap.ofList ([(x, t)]))))

-- 2. FIVE RULES:
| exp :     ∀ {A B},          Γ ⊢ A             →   Γ ⊢ B∨₁A           -- Expansion Rule
| contrac : ∀ {A},            Γ ⊢ (A∨₁A)        →   Γ ⊢ A
| assoc :   ∀ {A B C},        Γ ⊢ (A∨₁(B∨₁C))   →   Γ ⊢ (A∨₁B)∨₁C
| cut :     ∀ {A B C},        Γ ⊢ (A∨₁B)        →   Γ ⊢ ((¬₁A)∨₁C)      →   Γ ⊢ (B∨₁C)
| forallInt : ∀ {A B},        Γ ⊢ (A∨₁B)        →   Γ ⊢ ((∀₁ x A)∨₁B)

-- 3. AXIOMS:
| AxE₁:                       Γ ⊢ AxiomE1 x
| AxE₂:                       Γ ⊢ AxiomE2 x₁ x₂ A hA
| AxU:                        Γ ⊢ AxiomUn x t A
| AxC₁:                       Γ ⊢ AxiomC1 x₁ x₂       -- AxC₁ in the context of the axiomatic of the star combinatory calculus
                                                      -- ∀x₁,x₂ [(Π·x₁)·x₂ = x₁] is provable from Γ
| AxC₂:                       Γ ⊢ AxiomC2 x₁ x₂ x₃
| AxP₁:                       Γ ⊢ AxiomP1 x₁ x₂
| AxP₂:                       Γ ⊢ AxiomP2 x₁ x₂ x₃
| AxS₁:                       Γ ⊢ AxiomS1 x₁ x₂
| AxS₂:                       Γ ⊢ AxiomS2 x₁ x₂ x₃
| AxS₃:                       Γ ⊢ AxiomS3 x₁ x₂ x₃ y
| AxS₄:                       Γ ⊢ AxiomS4 x₁ x₂

-- 4. AUXILLIARY AXIOM SCHEME:
| AxbAC    : ∀ {Γ A},         A ∈ Γ             → Γ ⊢ A


--axiom AxE₁_term {Γ : Set Formula} (t:Term): Γ ⊢ (t=₁t)
axiom AxE₂_term {Γ : Set Formula} (x x₁:String) (t :Term) (A:Formula) (hA : isBase A) :       Γ ⊢ (((var x₁)=₁t) ∧₁ (A →₁ (A.subst (HashMap.ofList ([x].zip [t])))))
axiom AxU_term {Γ : Set Formula} (x : String) (t : Term) (A : Formula) :                      Γ ⊢ ((b∀₁₁ x t A) ↔₁ (∀₁₁ x (((var x) ∈₁ t) →₁ A)))
axiom AxC₁_term {Γ : Set Formula} (t₁ t₂ : Term) :                                            Γ ⊢ ((Π₁·t₁)·t₂) =₁ t₁
axiom AxC₂_term {Γ : Set Formula} (t₁ t₂ t₃ : Term) :                                         Γ ⊢ (((Σ₁·t₁)·t₂)·t₃) =₁ (t₁·t₃)·(t₂·t₃)
axiom AxP₁_term {Γ : Set Formula} (t₁ t₂ : Term) :                                            Γ ⊢ (((i∪₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁))
axiom AxP₂_term {Γ : Set Formula} (t₁ t₂ t₃ : Term) :                                         Γ ⊢ (((i∪₁·((∪₁·t₁)·t₂))·t₃) =₁ ((∪₁·((i∪₁·t₁)·t₃))·((i∪₁·t₂)·t₃)))
axiom AxS₁_term {Γ : Set Formula} (t₁ t₂ : Term) :                                            Γ ⊢ ((t₁ ∈₁ (𝔰₁·t₂)) ↔₁ (t₁ =₁ t₂))
axiom AxS₂_term {Γ : Set Formula} (t₁ t₂ t₃ : Term) :                                         Γ ⊢ ((t₁ ∈₁ ((∪₁·t₂)·t₃) ) ↔₁ ((t₁ ∈₁ t₂) ∨₁ (t₁ ∈₁ t₃)))
axiom AxS₃_term {Γ : Set Formula} (x:String) (a f b : Term) :                                 Γ ⊢ ((b ∈₁ ((i∪₁·a)·f)) ↔₁ (b∃₁₁ x a (b ∈₁ (f·(var x)))))
axiom AxS₄_term {Γ : Set Formula} (x:String) (t : Term) :                                     Γ ⊢ (b∃₁₁ x t ((var x) ∈₁ t))

end

-- NEW NOTATION:
infix:27 (priority := high) " ⊢ " => ProvableFrom     -- This is not the notation from ProvableFrom!

-- DEFINITION: A formula is said to be provable if it can be derived from an empty set of assumptions,
-- i.e. if it can be derived using ProvableFrom (inductive type) and nothing else.
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (exMid subs exp contrac assoc cut forallInt AxE₁ AxE₂ AxU AxC₁ AxC₂ AxP₁ AxP₂ AxS₁ AxS₂ AxS₃ AxS₄)
variable {Γ : Set Formula}

-- ---------------------------------------
-- MODUS PONENS
-- ---------------------------------------

lemma ModusPonens {Γ : Set Formula} (A B : Formula) (hA : Γ ⊢ A) (hnAvB : Γ ⊢ (A→₁B)) :
  --Γ ⊢ A  →
  --Γ ⊢ (A→₁B) →
  --------------
  Γ ⊢ B :=
by
  unfold F_implies at hnAvB
  have hBvA := @exp Γ A B hA
  have hBvnB := @exMid Γ B
  have hAvB := @cut Γ B A B hBvA hBvnB
  have hBvB := @cut Γ A B B hAvB hnAvB
  exact contrac hBvB

-- ---------------------------------------
-- AUXILLIARY AXIOMS
-- ---------------------------------------

axiom Add1 (Γ : Set Formula) (A B : Formula) :
  Γ ⊢ A  →
  Γ ⊢ B  →
  --------------
  Γ ⊢ A∧₁B

axiom Add2 (Γ : Set Formula) (A : Formula) :
  A ∈ Γ
  --------------
  → Γ ⊢ A

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

-- ---------------------------------------
-- AXIOMS FOR TERMS
-- ---------------------------------------

open axioms

lemma Aux1 (x : String) (t : Term) :
 ((var x=₁var x).subst (mkHashMap.insert x t)) = (t=₁t) := by sorry

lemma AxE₁_term_l {Γ : Set Formula} (x:String) (t:Term): Γ ⊢ (t=₁t) :=
by
  have H := @AxE₁ Γ x
  unfold AxiomE1 at H; unfold AxiomE1_matrix at H
  have hSubs := @subs Γ x t ((var x) =₁ (var x))
  have hMP := @ModusPonens Γ (∀₁₁ x ((var x)=₁(var x))) (((var x)=₁(var x)).subst (HashMap.ofList [(x, t)])) H hSubs
  simp [HashMap.ofList, HashMap.empty, Aux1] at hMP
  exact hMP

lemma AxC₁_term_l {Γ : Set Formula} {x₁ x₂ : String} (t₁ t₂ : Term) :   Γ ⊢ (((Π₁·t₁)·t₂) =₁ t₁) :=
by
  have H := @AxC₁ Γ x₁ x₂
  --have H2 := @AxiomC1 x₁ x₂
  unfold AxiomC1 at H; unfold AxiomC1_matrix at H
  have hSubs := @subs Γ x₁ t₁ (∀₁₁ x₂ (((Π₁·var x₁)·var x₂)=₁var x₁))
  sorry

lemma AxC₂_term_l {Γ : Set Formula} {x₁ x₂ x₃ : String} (t₁ t₂ t₃ : Term) :  Γ ⊢ ((((Σ₁·t₁)·t₂)·t₃) =₁ ((t₁·t₃)·(t₂·t₃))) := by sorry


-- ---------------------------------------
-- EQUALITY: Symmetry and Transitivity
-- ---------------------------------------

-- Symmetry of equality
lemma eq_symm_var (x₁ x₂ : String) (Γ : Set Formula) :
  Γ ⊢ ∀₁ [x₁,x₂] (((var x₁) =₁ (var x₂))→₁((var x₂) =₁ (var x₁))) := by sorry

lemma eq_symm_term (t₁ t₂ : Term) (Γ : Set Formula) :
  Γ ⊢ ((t₁ =₁ t₂)→₁(t₂ =₁ t₁)) := by sorry

-- Transitivity of equality
lemma eq_trans_var (x₁ x₂ x₃: String) (Γ : Set Formula) :
  Γ ⊢ ∀₁ [x₁,x₂,x₃] ((((var x₁)=₁(var x₂))∧₁((var x₂)=₁(var x₃)))→₁((var x₁)=₁(var x₃))) := by sorry

lemma eq_trans_term (t₁ t₂ t₃ : Term) (Γ : Set Formula) :
  Γ ⊢ (((t₁=₁t₂)∧₁(t₂=₁t₃))→₁(t₁=₁t₃)) := by sorry


-- -------------------------------------------------------------
-- AXIOM 1.8 (p.18):
-- Bounded Axiom of Choice
-- -------------------------------------------------------------

def bAC (x y f a b : List String) (A : Formula) : Formula :=
  ((∀₁ x (∃₁ y A)) →₁ (∃₁ f (∀₁ a (b∃₁ b ((f.tt)⊙(a.tt)) A))))            -- bAC^ω_*

def bAC_star_om (x y f a b : String) (A : Formula) : Formula :=
  ((∀₁₁ x (∃₁₁ y A)) →₁ (∃₁₁ f (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A))))     -- bAC^ω_* (for Strings)
