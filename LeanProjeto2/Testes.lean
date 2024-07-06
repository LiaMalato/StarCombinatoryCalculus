import LeanProjeto2.StarLang_old

open StarLang
open FType

#check ground

-- EXAMPLE 1.2
def ex1Type1 : FType := star ground                                                         -- 1.2.1 G*
def ex1Type2 : FType := ground ⟶ ground                                                 -- G → G
def ex1Type31 : FType := arrow ground (arrow ground ground)                                 -- G → (G → G)
def ex1Type32 : FType := arrow (arrow ground ground) ground                                 -- (G → G) → G
def ex1Type4 : FType := arrow (arrow ground ground) (arrow ground (arrow ground ground))    -- (G → G) → (G → (G → G))
def ex1Type51 (σ τ : FType) : FType := arrow σ (arrow (arrow (star σ) τ) τ)                 -- σ → ((σ* → τ) → τ)
def ex1Type52 (σ τ : FType) : FType := star (arrow (star σ) τ)                              -- 1.2.5 (σ* → τ)*
example (σ τ : FType) : FType := star (arrow (star σ) τ)

#check ex1Type32 -- ???????????
#check ex1Type51

-- --------------------------------------------------------------------------

-- PRIMEIRA DEFINIÇAO DE CONSTANTES (not good enough, use inductive)

-- Combinador Pi -- Π : σ → (τ → σ) -- [def 1.2 b) i.]
def Pi (σ τ : FType) : FType :=
  arrow σ (arrow τ σ)

-- Combinador Sigma -- Σ : (σ → (τ → ρ)) → ((σ → τ) → (σ → ρ)) -- [def 1.2 b) ii.]
def Sigma_ (σ τ ρ : FType) : FType :=
  arrow (arrow σ (arrow τ ρ)) (arrow (arrow σ τ) (arrow σ ρ))

-- Singleton -- s_σ : σ → σ* -- [def 1.2 c) i.]
def singg (σ : FType) : FType :=
  arrow σ (star σ)

-- Union (binary) -- ∪_σ : σ* → (σ* → σ*) -- [def 1.2 c) ii.]
def bUnion (σ : FType) : FType :=
  arrow (star σ) (arrow (star σ) (star σ))

-- Indexed union -- σ* → ((σ → τ*) → τ*) -- [def 1.2 c) iii.]
def iUnion (σ τ : FType) : FType :=
  arrow (star σ) (arrow (arrow σ (star τ)) (star τ))

-- --------------------------------------------------------------------------

-- SIMBOLOS

inductive Symb
| and
| not
| unbForall
| tEq
| memb
| bForall


inductive P : Prop
| x
| y

--lemma a (x:P) : P := by
--  constructor


-- AXIOMS SEM NOTAÇAO

open Term
open AtomicFormula

def AxC₁ (σ : FType) (p q : Term) : AtomicFormula       -- FALTA TYPECHECKING
  := eq σ (app (app Π₁ p) q) q
--:= eq σ ((Π₁·p)·q) q

def AxC₂ (τ : FType) (p q t : Term) : AtomicFormula     -- FALTA TYPECHECKING
  := eq τ (app (app (app Σ₁ p) q) t) (app (app p t) (app q t))
--:= eq τ (((Σ₁·p)·q)·t) ((p·t)·(q·t))

def AxP₁ (τ : FType) (x y : Term) : AtomicFormula
  := eq (τ⋆) (app (app ind_⋃₁ (app 𝔰₁ x)) y) (app x y)
--:= eq (τ⋆) ((ind_⋃₁ · (𝔰₁·x)) · y) (x·y)

def AxP₂ (τ : FType) (x y z : Term) : AtomicFormula
  := eq (τ⋆) (app (app ind_⋃₁ (app (app ∪₁ x) y) ) z) (app (app ∪₁ (app (app ind_⋃₁ x) z)) (app (app ind_⋃₁ y) z))
--:= eq (τ⋆) ((ind_⋃₁ · ((∪₁·x)·y))·z) ((∪₁·((ind_⋃₁ · x)·z))·((ind_⋃₁ · y)·z))



/-
inductive Conversions
| C1 (t₁ t₂ : Term)
| C2 (t₁ t₂ t₃ : Term)
| C3 (t₁ t₂ : Term)
| C4 (t₁ t₂ t₃ : Term)

--def conversin : Expr → Int
--| C1 t₁ t₂      => t₁
--| C2 t₁ t₂ t₃   => (t₁·t₃)·(t₂·t₃)
--| C3 t₁ t₂      => t₂·t₁
--| C4 t₁ t₂ t₃   => (∪₁·((ind_⋃₁·t₁)·t₃))·((ind_⋃₁·t₂)·t₃)

-- def C1 (t₁ t₂ : Term) : Term := ((Π₁·t₁)·t₂) => t₁
-/
