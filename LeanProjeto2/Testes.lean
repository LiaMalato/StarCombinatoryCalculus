import LeanProjeto2.StarLang

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
