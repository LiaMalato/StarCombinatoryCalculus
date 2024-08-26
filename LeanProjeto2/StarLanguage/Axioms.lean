-- -------------------------------------------------------------
--            STAR LANGUAGE - AXIOMS
-- -------------------------------------------------------------

-- We import the definitions from the first-order language L:
import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.Syntax
import MathLib.Tactic

open FOLang
open LFormula
open Term
open Formula


-- --------------------------------------
-- --------------------------------------
-- ------------- AXIOMS -----------------
-- --------------------------------------
-- --------------------------------------

--def normal_form (A B : Formula) (x: String) : Formula → Formula
--| or A B => A
--| bForall x A => A
--| t => t

-- Drei strescher ass gleich, wees net wei dat heescht, syntactic equality
inductive Equivalent : Formula → Formula → Prop
| id : Equivalent A A
| comm : Equivalent A B → Equivalent B A
| double_neg : Equivalent (¬₁(¬₁A)) A
| comm_or : Equivalent (A∨₁B) (B∨₁A)                              -- TODO: the same with other obvious stuff
--| nf_left : Equivalent A B → Equivalent (normal_form A) B
--| nf_right : Equivalent A B → Equivalent A (normal_form B)

-- ---------------------------------------------------------------------------------
-- -------------------------------   AXIOMATIC   -----------------------------------
-- ---------------------------------------------------------------------------------

-- Reunião: acrescentar construtor para dizer que tem ou não freevars

/- ISTO
inductive Logic
| PL
| PL_bAC
-/

--ISTO inductive isTrue {L:Logic} : Formula → Prop
inductive isTrue : Formula → Prop
-- AXIOM SCHEMA (Shoenfield)
| lem :                                       -- A ∨ (¬A)
      isTrue (A ∨₁ (¬₁A))
| substitution {t:Term} {x:String} :          -- ∀x A(x) → A(t)
       --x ∈ xs →
       --closed_under_formula A xs →
       x ∈ A.freevars →
       isTrue (.unbForall x A) →
       --------------
       isTrue (substitution_formula x t A)

-- INFERENCE RULES (Shoenfield)
| expansion:                                  -- A => A∨B
      isTrue A →
      ---------------
      isTrue (A ∨₁ B)
| contraction :                               -- A∨A => A
      isTrue (A ∨₁ A) →
      ---------------
      isTrue A
| associativity :                             -- A∨(B∨C) => (A∨B)∨C
      isTrue (A ∨₁ (B ∨₁ C)) →
      ---------------
      isTrue ((A ∨₁ B) ∨₁ C)
| cut :                                       -- A∨B, (¬A)∨C => B∨C
      isTrue (A ∨₁ B) →
      isTrue ((¬₁A)∨₁C) →
      ---------------
      isTrue (B ∨₁ C)
| forall_introduction:                        -- A(x) ∨ B => ∀x A(x) ∨ B
      x ∈ A.freevars →
      isTrue (A ∨₁ B) →
      x ∉ B.freevars →                        -- provided that x does not occur free in B
      ---------------
      isTrue ((unbForall x A) ∨₁ B)

-- OTHER AXIOMS
| equivalence :
      (Equivalent A B) →
      isTrue A →
      isTrue B
| AxE₁ (x : String) :
    isTrue ((var x) =₁ (var x))
-- Problema yes: falta A(x) e A(y) -> criar notação?
--| AxE₂ (x y : String) (A : Formula) (h : x ∈ A.freevars): isTrue ((((var x) =₁ (var y))∧₁A) →₁ B) ∧ (y ∈ A.freevars)
--| AxE₂ (x y : String) : isTrue ((((var x) =₁ (var y))∧₁ A) →₁ A)        FALTA: falta x=y ∧ A(x) → A[substituition](y)
| Teste (x y : String) (A B : Formula) (h: x ∈ A.freevars) (Hy : y∉A.freevars) (HB : B = (substitution_formula x (var y) A)): isTrue ((((var x) =₁ (var y))∧₁A) →₁ B)
| AxU (x : String) (t : Term) (A : Formula) :
    isTrue ((b∀₁₁ x t A) ↔₁ (∀₁₁ x (((var x) ∈₁ t) →₁ A)))
| AxC₁ (t₁ t₂ : Term) :                                         -- TODO: mudar isto tudo para variables em vez de terms
    isTrue (((Π₁·t₁)·t₂) =₁ t₁)
| AxC₂ (t₁ t₂ t₃ : Term) :
    isTrue ((((Σ₁·t₁)·t₂)·t₃) =₁ ((t₁·t₃)·(t₂·t₃)))
| AxP₁ (t₁ t₂ : Term) :
    isTrue (((ind_⋃₁·(𝔰₁·t₁))·t₂) =₁ (t₂·t₁))
| AxP₂ (t₁ t₂ t₃ : Term) :
    isTrue (((ind_⋃₁·((∪₁·t₁)·t₂))·t₃) =₁ ((∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)))
| AxS₁ (t₁ t₂ : Term) :
    isTrue ((t₁ ∈₁ (𝔰₁·t₂)) ↔₁ (t₁ =₁ t₂))
| AxS₂ (t₁ t₂ t₃ : Term) : isTrue ((t₁ ∈₁ ((∪₁·t₂)·t₃) ) ↔₁ ((t₁ ∈₁ t₂) ∨₁ (t₁ ∈₁ t₃)))
| AxS₃ (a f b : Term) : isTrue ((b ∈₁ ((ind_⋃₁·a)·f)) ↔₁ (b∃₁₁ x a (b ∈₁ (f·(var x)))))
| bAC {x y f : String} : isTrue ((∀₁₁ x (∃₁₁ y A)) →₁ (∃₁₁ f (∀₁₁ x (b∃₁₁ y ((Term.var f)·(Term.var x)) A))))    -- bAC^ω_*
-- ISTO | bAC {x y f : String} {H:L=Logic.PL_bAC}: isTrue ((V₁ x (E₁ y A)) →₁ (E₁ f (V₁ x (bE₁ y ((Term.var f)·(Term.var x)) A))))    -- bAC^ω_*
-- Sempre que for para usar o isTrue é preciso escolher a lógica!






-- TESTE: o lemma eq_symmetry está a dar erro, mas o teste com #check mostra que a sintaxe está good
def f : Term := var "f"
def g : Term := var "g"

#check (f =₁ g) →₁ (g =₁ f)

-- Problema: this ↓ is not working
--lemma eq_symmetry (p q : Term): (p =₁ q) := sorry
lemma eq_symmetry : ∀(p q:Term), isTrue ((p=₁q)→₁(q=₁p)) := sorry -- construtores de isTrue
-- ISTO lemma eq_symmetry : ∀(p q:Term), isTrue (L := Logic.PL) ((p=₁q)→₁(q=₁p)) := sorry -- construtores de isTrue

--theorem tastino (x y : String) : Formula

--lemma eq_symmetry (x y : String) : (((var x) =₁ (var y)) →₁ ((var y) =₁ (var x))) := sorry

--lemma eq_transitivity (x y z : String) : ((((var x) =₁ (var y)) ∧₁ ((var y) =₁ (var z))) →₁ ((var x) =₁ (var z))) := sorry


/- Tarefas:
      1. Pegar nos isTrue e definir algo para tuple of terms
      2. Precisamos de lemas auxiliares para conseguir mexer no que está dentro do isTrue?
      3. Prove estes mini lemmas/theorem
-/
