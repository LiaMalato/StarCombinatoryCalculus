import LeanProjeto2.StarLang

open StarLang
open FType
open Term

-- --------------------
-- TERMOS E CONSTANTES
-- --------------------

-- EXAMPLE 1.2 (p.5)
def s1ex2_1 : FType := G⋆
def s1ex2_2 : FType := G ⟶ G
def s1ex2_3 : FType := G ⟶ (G ⟶ G)
def s1ex2_3' : FType := (G ⟶ G) ⟶ G
def s1ex2_4 : FType := (G ⟶ G) ⟶ (G ⟶ (G ⟶ G))
def s1ex2_5 (σ τ : FType) : FType := σ ⟶ ((σ⋆ ⟶ τ) ⟶ τ)
def s1ex2_5' (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆
example (σ τ : FType) : FType := (σ⋆ ⟶ τ)⋆

#check s1ex2_3' -- ???????????
#check s1ex2_5





-- -------------------------------------
-- EXAMPLE 1.3: cenas com tuples (tipos)
-- -------------------------------------




-- -------------------------
-- EXAMPLE 1.4: (p.10-11)
--  p: (σ → τ) → τ → ρ
--  q : σ ⟶ τ ⟶ ρ
--  r : ρ ⟶ σ
--  s : ρ ⟶ σ
--  t : σ → τ
--  w : σ ⟶ τ⋆
--  x : σ
--  y : τ
-- -------------------------

-- Ex1.4(1). t₁t₂ : τ where t₁ : σ → τ and t₂ : σ
example (σ τ : FType) (t₁ t₂ : Term) (h1: TypeChecking t₁ (σ ⟶ τ)) (h2 : TypeChecking t₂ σ) : TypeChecking (app t₁ t₂) τ :=
  by
    exact TypeChecking.tcApp h1 h2

-- Ex1.4(1). tx : τ where t : σ → τ and x : σ
example (σ τ : FType) (t : Term) (x : string) (h1: TypeChecking t (σ ⟶ τ)) (h2 : TypeChecking (var x) σ) : TypeChecking (app t (var x)) τ :=
  by
   exact TypeChecking.tcApp h1 h2

-- Ex1.4(2). (pt)(tx) : ρ where p: (σ → τ) → τ → ρ, t : σ → τ and x : σ
example (σ τ ρ : FType) (p t : Term) (x: string) (h1 : TypeChecking p ((σ⟶τ)⟶τ⟶ρ)) (h2: TypeChecking t (σ ⟶ τ)) (h3 : TypeChecking (var x) σ) : TypeChecking (app (app p t) (app t (var x))) ρ :=
  by
    have H1 := TypeChecking.tcApp h1 h2
    have H2 := TypeChecking.tcApp h2 h3
    exact TypeChecking.tcApp H1 H2

-- Ex1.4(3) - Π₁_{σ,τ} x : τ ⟶ σ where Π₁ : σ ⟶ τ ⟶ σ and x : σ
example (σ τ : FType) (t : Term) (x : string)
    (h1 : TypeChecking (var x) σ)
    (h2 : TypeChecking Π₁ (σ ⟶ τ ⟶ σ)) : TypeChecking (app Π₁ (var x)) (τ ⟶ σ) :=
  by
    exact TypeChecking.tcApp h2 h1


-- Ex1.4(4) - (Σ₁_{σ,τ,ρ} q)t : ρ ⟶ τ where Σ₁ : (σ ⟶ τ ⟶ ρ) ⟶ (σ ⟶ τ) ⟶ σ ⟶ ρ and t : σ ⟶ τ and x : σ
example (σ τ ρ : FType) (q t : Term)
    (ht : TypeChecking t (σ ⟶ τ))
    (hq : TypeChecking q (σ ⟶ τ ⟶ ρ))
    (hs : TypeChecking Σ₁ ((σ ⟶ (τ ⟶ ρ)) ⟶ ((σ ⟶ τ) ⟶ (σ ⟶ ρ)))) : TypeChecking (app (app Σ₁ q) t) (σ ⟶ ρ) :=
  by
    have H1 := TypeChecking.tcApp hs hq
    exact TypeChecking.tcApp H1 ht

-- Ex1.4(5) -
example (σ τ : FType) (t : Term) (x: string)
    (ht : TypeChecking t (σ ⟶ τ))
    (hx : TypeChecking (var x) σ)
    (h_sig : TypeChecking Σ₁ ((σ ⟶ τ ⟶ σ) ⟶ (σ ⟶ τ) ⟶ σ ⟶ σ))
    (h_pi : TypeChecking Π₁ (σ ⟶ τ ⟶ σ)): TypeChecking (app (app (app Σ₁ Π₁) t) (var x)) σ :=
  by
    have H1 := TypeChecking.tcApp h_sig h_pi
    have H2 := TypeChecking.tcApp H1 ht
    exact TypeChecking.tcApp H2 hx

-- Ex1.4(6) -
example (σ τ : FType) (w : Term) (x: string)
    (hw : TypeChecking w (σ ⟶ τ⋆))
    (hx : TypeChecking (var x) σ)
    (h_sing : TypeChecking 𝔰₁ (σ ⟶ σ⋆))
    (h_i_un : TypeChecking ind_⋃₁ (σ⋆ ⟶ ((σ ⟶ τ⋆) ⟶ τ⋆)))
    (h_b_un : TypeChecking ∪₁ (τ⋆ ⟶ (τ⋆ ⟶ τ⋆))) : TypeChecking (app ∪₁ (app (app ind_⋃₁ (app 𝔰₁ (var x))) w)) (τ⋆ ⟶ τ⋆) :=
  by
    have H1 := TypeChecking.tcApp h_sing hx
    have H2 := TypeChecking.tcApp h_i_un H1
    have H3 := TypeChecking.tcApp H2 hw
    exact TypeChecking.tcApp h_b_un H3


-- ----------------------------------------------
-- EXAMPLE 1.5: cenas com tuples (termos e tipos)
-- ----------------------------------------------







-- --------------------
-- FORMULAS
-- --------------------

open AtomicFormula
open BaseFormula
open Formula


-- --------------------
-- AXIOMS
-- --------------------

-- Shoenfield's calculus




-- Combinator axioms





-- Primary axioms for the star constants





-- Secondary axioms for the star constants





-- Bounded axiom of choice
