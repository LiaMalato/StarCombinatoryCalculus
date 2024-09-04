-- -------------------------------------------------------------
--            STAR LANGUAGE - AXIOMS (new)
--          Versão adaptada de Patrick Massot
-- -------------------------------------------------------------

import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.SHFunctInterp
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Batteries
import MathLib.Tactic

open FOLang
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

def axiomE1 (x : String) : Formula :=
  (var x)=₁(var x)
def axiomE2 (x₁ x₂ : String) (A : Formula) (hA : isBase A) : Formula :=
  (((var x₁)=₁(var x₂)) ∧₁ A) →₁ (A.subst (HashMap.ofList ([x₁].zip ([x₂].tt))))
def axiomUn (x : String) (t : String) (A : Formula) : Formula :=
  (b∀₁₁ x (var t) A) ↔₁ (∀₁₁ x (((var x) ∈₁ (var t)) →₁ A))
def axiomC1 (x₁ x₂ : String) : Formula :=
  ((Π₁·(var x₁))·(var x₂)) =₁ (var x₁)
def axiomC2 (x₁ x₂ x₃ : String) : Formula :=
  (((Σ₁·(var x₁))·(var x₂))·(var x₃)) =₁ (((var x₁)·(var x₃))·((var x₂)·(var x₃)))
def axiomP1 (x₁ x₂ : String) : Formula :=
  ((ind_⋃₁·(𝔰₁·(var x₁)))·(var x₂)) =₁ ((var x₂)·(var x₁))
def axiomP2 (x₁ x₂ x₃ : String) : Formula :=
  ((ind_⋃₁·((∪₁·(var x₁))·(var x₂)))·(var x₃)) =₁ ((∪₁·((ind_⋃₁·(var x₁))·(var x₃)))·((ind_⋃₁·(var x₂))·(var x₃)))
def axiomS1 (x₁ x₂ : String) : Formula :=
  ((var x₁) ∈₁ (𝔰₁·(var x₂))) ↔₁ ((var x₁) =₁ (var x₂))
def axiomS2 (x₁ x₂ x₃ : String) : Formula :=
  ((var x₁) ∈₁ ((∪₁·(var x₂))·(var x₃)) ) ↔₁ (((var x₁) ∈₁ (var x₂)) ∨₁ ((var x₁) ∈₁ (var x₃)))
def axiomS3 (b a f x : String) : Formula :=
  ((var b) ∈₁ ((ind_⋃₁·(var a))·(var f))) ↔₁ (b∃₁₁ x (var a) ((var b) ∈₁ ((var f)·(var x))))
def axiomS4 (x₁ x₂ : String) : Formula :=
  b∃₁₁ x₂ (var x₁) ((var x₂) ∈₁ (var x₁))


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


/-
LEMAS: A MAIORIA DOS AXIOMAS SÃO UNIV CLOSURES DE BASE FORMULAS
-/

open Formula
open isAtomic
open isBase

-- On AxiomE1:
lemma AxiomE1_univ_of_base (x:String) : (isBase (axiomE1 x)) := by
  unfold axiomE1
  exact b_atom (isAtomic.at_eq (var x) (var x))

#check Axioms.AxiomE1_univ_of_base "x"

example : (axiomE1 "x").components2 = ([], [], (axiomE1 "x")) := by
  exact rfl

/-
#check SH_int2
def HHH {x₁ x₂ : String} {int_axC1 : Formula} : Prop := SH_int2 (axiomC1 x₁ x₂) int_axC1
--#check axiomE1
def HHHH := (axiomE1 "x").components2
#eval (axiomE1 "x").components2

def HHH : Prop := SH_int2 (axiomC1 x₁ x₂) int_axC1
example
  (hInt : SH_int2 (axiomC1 x₁ x₂) int_axC1)
  (hComp : (a,b,mat_axC1) = int_axC1.components2) :
  (a = ∅) ∧ (b = ∅) := by sorry
-/


-- On AxiomE2:
lemma AxiomE2_univ_of_base : (isBase (axiomE2 x₁ x₂ A hA)) := by
  unfold axiomE2
  have H1 := Subst_isBase A hA [x₁] [x₂].tt
  have H2 := b_atom (isAtomic.at_eq (var x₁) (var x₂))
  have H3 := Conj_base ((var x₁)=₁(var x₂)) A H2 hA
  exact Imp_base ((var x₁=₁var x₂)∧₁A) (A.subst (HashMap.ofList ([x₁].zip [x₂].tt))) H3 H1

example : (axiomE2 x₁ x₂ A hA).components2 = ([], [], (axiomE2 x₁ x₂ A hA)) := by sorry

-- COMMENT: AxiomUn_univ_of_base não dá porque axiomUn não é base :)

lemma AxiomC1_univ_of_base : (isBase (axiomC1 x₁ x₂)) := by
  unfold axiomC1
  exact b_atom (isAtomic.at_eq ((Π₁·var x₁)·var x₂) (var x₁))

lemma AxiomC2_univ_of_base : (isBase (axiomC2 x₁ x₂ x₃)) := by
  unfold axiomC2
  exact b_atom (isAtomic.at_eq (((Σ₁·(var x₁))·(var x₂))·(var x₃)) (((var x₁)·(var x₃))·((var x₂)·(var x₃))))

lemma AxiomP1_univ_of_base : (isBase (axiomP1 x₁ x₂)) := by
  unfold axiomP1
  exact b_atom (isAtomic.at_eq ((ind_⋃₁·(𝔰₁·(var x₁)))·(var x₂)) ((var x₂)·(var x₁)))

lemma AxiomP2_univ_of_base : (isBase (axiomP2 x₁ x₂ x₃)) := by
  unfold axiomP2
  exact b_atom (isAtomic.at_eq ((ind_⋃₁·((∪₁·(var x₁))·(var x₂)))·(var x₃)) ((∪₁·((ind_⋃₁·(var x₁))·(var x₃)))·((ind_⋃₁·(var x₂))·(var x₃))))

lemma AxiomS1_univ_of_base : (isBase (axiomS1 x₁ x₂)) := by
  unfold axiomS1
  have H1 := b_atom (isAtomic.at_mem (var x₁) (𝔰₁·(var x₂)))
  have H2 := b_atom (isAtomic.at_eq (var x₁) (var x₂))
  exact Iff_base (var x₁∈₁𝔰₁·var x₂) (var x₁=₁var x₂) H1 H2

lemma AxiomS2_univ_of_base : (isBase (axiomS2 x₁ x₂ x₃)) := by
  unfold axiomS2
  have H1 := b_atom (isAtomic.at_mem (var x₁) ((∪₁·(var x₂))·(var x₃)))
  have H2 := b_atom (isAtomic.at_mem (var x₁) (var x₂))
  have H3 := b_atom (isAtomic.at_mem (var x₁) (var x₃))
  have H4 := b_or H2 H3
  exact Iff_base (var x₁∈₁(∪₁·var x₂)·var x₃) ((var x₁∈₁var x₂).or (var x₁∈₁var x₃)) H1 H4

lemma AxiomS3_univ_of_base {f:String} : (isBase (axiomS3 b a f x)) := by
  unfold axiomS3
  have H1 := b_atom (isAtomic.at_mem (var b) ((ind_⋃₁·(var a))·(var f)))
  have H2 := b_atom (isAtomic.at_mem (var b) ((var f)·(var x)))
  have H3 := bExists_base x (var a) H2
  exact Iff_base (var b∈₁(ind_⋃₁·var a)·var f) (b∃₁₁ x (var a) (var b∈₁var f·var x)) H1 H3

lemma AxiomS4_univ_of_base : (isBase (axiomS4 x₁ x₂)) := by
  unfold axiomS4
  have H := b_atom (isAtomic.at_mem (var x₂) (var x₁))
  exact bExists_base x₂ (var x₁) H








def AxiomE1 (x : String) : Formula :=
  ∀₁₁ x (axiomE1 x)
def AxiomE2 (x₁ x₂ : String) (A : Formula) (hA : isBase A) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (axiomE2 x₁ x₂ A hA))
def AxiomUn (x : String) (t : String) (A : Formula) : Formula :=
  ∀₁₁ t (axiomUn x t A)
def AxiomC1 (x₁ x₂ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (axiomC1 x₁ x₂))
def AxiomC2 (x₁ x₂ x₃ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (∀₁₁ x₃ (axiomC2 x₁ x₂ x₃)))
def AxiomP1 (x₁ x₂ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (axiomP1 x₁ x₂))
def AxiomP2 (x₁ x₂ x₃ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (∀₁₁ x₃ (axiomP2 x₁ x₂ x₃)))
def AxiomS1 (x₁ x₂ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (axiomS1 x₁ x₂))
def AxiomS2 (x₁ x₂ x₃ : String) : Formula :=
  ∀₁₁ x₁ (∀₁₁ x₂ (∀₁₁ x₃ (axiomS2 x₁ x₂ x₃)))
def AxiomS3 (b a f x : String) : Formula :=
  ∀₁₁ a (∀₁₁ f (∀₁₁ b (axiomS3 b a f x)))
def AxiomS4 (x₁ x₂ : String) : Formula :=
  ∀₁₁ x₁ (axiomS4 x₁ x₂)



#eval (axiomE1 "x").components2
-- Quero mostrar que pôr foralls antes dos axiomas, que não muda nada
-- que SH_int2 de axiomE1 que é a mesma coisa que SH_int2 de AxiomE1
--#eval
#eval (AxiomE1 "x").components2
--#eval SH_int2 (AxiomE1 "x")







/- PARA COPIAR
lemma Axiom_univ_of_base : (isBase ()) := by sorry
-/



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
def BAxiomS3 (b a f x : String) : Formula :=
  ∀₁ [a, f, b]          (((var b) ∈₁ ((ind_⋃₁·(var a))·(var f))) ↔₁ (b∃₁₁ x (var a) ((var b) ∈₁ ((var f)·(var x)))))
def BAxiomS4 (x₁ x₂ : String) : Formula :=
  ∀₁ [x₁]               (b∃₁₁ x₂ (var x₁) ((var x₂) ∈₁ (var x₁)))

end Axioms

--def Axreflexivity (x : String) : Formula := (Term.var x) =₁ (Term.var x)


/-
lemma AxiomE1_univ_of_base (x : String) : (isBase ((var x)=₁(var x))) := by
  exact b_atom (isAtomic.at_eq (var x) (var x))
-/



section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` is the predicate that there is a proof tree with conclusion `A` with assumptions from
  `Γ`. This is a typical list of rules for natural deduction with classical logic. -/


-- Reflexivity axiom

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
| AxS₃ {f:String}:            Γ ⊢ AxiomS3 a f b x
| AxS₄:                       Γ ⊢ AxiomS4 x₁ x₂

-- ax, exMid, subs, exp, contrad, assoc, cut, forallInt, AxE₁, AxE₂, AxU, AxC₁, AxC₂, AxP₁, AxP₂, AxS₁, AxS₂, AxS₃, AxS₄

/-
| AxE₁ (t:Term) :                               Γ ⊢ (t=₁t)
| AxE₂ (t₁ t₂ :Term) (hA : isBase A) :          Γ ⊢ ((t₁=₁t₂) ∧₁ (A →₁ A))     -- TBD: falta substituição aqui
| AxU (x : String) (t : Term) (A : Formula) :   Γ ⊢ ((b∀₁₁ x t A) ↔₁ (∀₁₁ x (((var x) ∈₁ t) →₁ A)))
| AxC₁ (t₁ t₂ : Term) :                         Γ ⊢ (((Π₁·t₁)·t₂) =₁ t₁)
| AxC₂ (t₁ t₂ t₃ : Term) :                      Γ ⊢ ((((Σ₁·t₁)·t₂)·t₃) =₁ ((t₁·t₃)·(t₂·t₃)))
| AxP₁ (t₁ t₂ : Term) :                         Γ ⊢ (((ind_⋃₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁))
| AxP₂ (t₁ t₂ t₃ : Term) :                      Γ ⊢ (((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) =₁ ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)))
| AxS₁ (t₁ t₂ : Term) :                         Γ ⊢ ((t₁ ∈₁ (𝔰₁·t₂)) ↔₁ (t₁ =₁ t₂))
| AxS₂ (t₁ t₂ t₃ : Term) :                      Γ ⊢ ((t₁ ∈₁ ((∪₁·t₂)·t₃) ) ↔₁ ((t₁ ∈₁ t₂) ∨₁ (t₁ ∈₁ t₃)))
| AxS₃ (a f b : Term) :                         Γ ⊢ ((b ∈₁ ((ind_⋃₁·a)·f)) ↔₁ (b∃₁₁ x a (b ∈₁ (f·(var x)))))
-- TBD: FALTA AXS4
-/

end

def bAC (x y f : List String) (A : Formula) : Formula := (∀₁ x (∃₁ y A)) →₁ (∃₁ f (∀₁ x (bExistsTuple2 y ((f.tt)⊙(x.tt)) A)))     -- bAC^ω_*


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

example (A : Formula) {f : List String} : (insert (bAC x y f B) ∅ ⊢ A) → (Provable A) := by sorry
theorem Soundness (A : Formula) {f : List String} : (insert (bAC x y f B) ∅ ⊢ A) → (∃(t: List Term), (Provable (∀₁ a A))) := by sorry    -- TBD: falta subst aqui
theorem Characterization (A : Formula) {f : List String} : (insert (bAC x y f B) ∅ ⊢ A) → (Provable (A ∨₁ A)) := by sorry          -- TBD: falta A^SH aqui
lemma Lem32 (A : Formula) (hA : isBase A) {f : List String}: (insert (bAC x y f B) ∅ ⊢ ((b∀₁ x t (∃₁ y A)) →₁ (∃₁ b (b∀₁ x t (bExistsTuple2 y (b.tt) A))))) := by sorry




/-
example : insert A (insert B ∅) ⊢ A ∧₁ B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_insert _ _)))

example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (by apply_ax) (by apply_ax)
-/




/-

/- A formula is provable if there is a -/
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}

-/
