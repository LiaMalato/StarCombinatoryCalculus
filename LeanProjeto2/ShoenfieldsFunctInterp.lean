import LeanProjeto2.FOL
import LeanProjeto2.StarLang
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

open FOL
open LFormula

open StarLang
--open FType

/- EXEMPLO BASE (a tirar depois)
--import LeanProjeto2.FOL
--open FOL
--open LFormula
example
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (c,d,B_SH)) (hB3 : StarLang.isBase B_SH) :
  (SH_int (  ) (Recreate ( , , ))) := by sorry
-/


-- SHOENFIELD'S FUNCTIONAL INTERPREATION

-- ---------------------------------------------------------------------------------------------------------------
--             SECTION 2.2: Shoenfield's functional interpretation
-- ---------------------------------------------------------------------------------------------------------------

-- -------------------------------------------------------------
-- DEFINITION 2.1 (p.38): Shoenfield's functional interpretation
-- -------------------------------------------------------------

/-
To define Shoenfield's functional interpretation we need some auxiliary functions to deal with the
different components of the interpretation of a formula. Every interpretation has a list of universal
variables, a list of existential variables and the matrix, i.e. the lower SH-formula (a base formula).
These three components will be represented by a tuple.

For example, if a formula A has the interpretation A^SH given by
                        ∀a ∃b A_SH(a,b)
then we would represent this as (a,b,A_SH).

The function 'components' transforms a formula such as ∀a ∃b A_SH(a,b) into the tupe (a,b,A_SH).
The function 'Recreate' transforms a tuple such as (a,b,A_SH) into the formula ∀a ∃b A_SH(a,b).

The function 'components_neg' is to deal with the negation.
-/

namespace StarLang.Formula

-- AUXILIARY FUNCTIONS:
-- TO DO / Problema : components não pode ser feito usando ∃ diretamente? Não, é o pattermatching

/-
def components_neg : Formula → (Finset String × Finset String × Formula)
| .unbForall x F => let (a,b,rest) := components_neg F;
                    (a,{x} ∪ b,rest)
| F => ({},{},F)
-/

def components : Formula → (Finset String × Finset String × Formula)
-- Reunião: daria se calhar para pôr aqui um not e forall
| .unbForall x F => let (a,b,rest) := components F;
                    ({x} ∪ a,b,rest)
| .not (.unbForall x F) => let (a,b,rest) := components F;
                           (a,{x} ∪ b,rest)
| .not F => components F
| F => ({},{},F)
-- Só se pode usar quando ja estiver com ∀a ∃b

-- Example to use components
def A_teste : Formula := Formula.rel "R" []
def exampleFormula : Formula :=
  bV₁ "x" (Term.var "t") (¬₁ (V₁ "y" A_teste))
#eval exampleFormula.components  -- Devia dar ({x}, {y}, A_teste), mas falta Repr -- TO DO / Problema

def formula_teste (A:Formula) : Formula := (V₁ "x" (E₁ "y" (E₁ "z" (¬₁A))))
#eval (formula_teste A_teste).components -- Devia dar ({x}, {y, z}, ¬₁A), mas falta Repr -- TO DO / Problema

-- ∀ a ∃ b [¬ (b∀)]

-- ∀ a ∃ b -> (a,b,...) --> b∀₁ a


end StarLang.Formula

noncomputable def recreate : (Finset String × Finset String × Formula) → Formula
| (a,b,rest) => -- Problema: Assim ficamos com (x,y,¬F) em vez de (x,y,F)
                let ex := List.foldl (fun f x => .not (.unbForall x f)) rest (b.val.toList : List String)
                List.foldl (fun f x => .unbForall x f) ex (a.val.toList : List String)

noncomputable def Recreate : (Finset String × Finset String × Formula) → Formula
| (a, b, rest) => -- Assim já ficamos com (x,y,F)
  -- Negações dentro do b
                let neg := List.foldl (fun f x => .unbForall x (.not f)) rest (b.val.toList : List String)
  -- unbForall dentro do a
                List.foldl (fun f x => .unbForall x f) neg (a.val.toList : List String)
-- TO DO / Problema: dá para acrescentar aqui que rest is always base? Fazer lema (Reunião)

-- --------------------------------------
-- DEFINITION 2.1 (p.38):
-- Shoenfield's functional interpretation
-- --------------------------------------

/-
Here we will represent an interpretation A^SH such as ∀a∃b A_SH(a,b) as
                  ( SH_int A^SH ( Recreate (a,b,A_SH) ) )
              ( SH_int upperSH ( Recreate (univ_var,exist_var,lowerSH) ) )
-/

-- TODO / Problema: variaveis disjuntas -> Reunião: na documentação ver se Finset já tem disjunto
-- a∪b∪c∪d : Finset     -> ver Disjoint a b c d
inductive SH_int : Formula → Formula → Prop
| base : (h : StarLang.isBase A) → (SH_int A (Recreate ({},{},A)))
| disj : SH_int A AuSH →          -- TODO: isto é preciso?
         SH_int B BuSH →
         AuSH.components = (a,b,A_SH) →                                     -- A^SH = ∀a ∃b A_SH(a,b)
         BuSH.components = (c,d,B_SH) →                                     -- B^SH = ∀c ∃d B_SH(c,d)
         --({a,b} ⊆ A.allvars) →                                            -- TO DO: precisamos?
         --({c,d} ⊆ B.allvars) →                                            -- TO DO: dizer lista não tem conjuntos repetidos
         (hA : StarLang.isBase A_SH) →
         (hB : StarLang.isBase B_SH) →
         (SH_int (A∨₁B) (Recreate (a∪c,b∪d,(A_SH ∨₁ B_SH))))                -- (A∨B)^SH = ∀a,c ∃b,d [ A_SH(a,b) ∨ B_SH(c,d) ]
| neg {f a':String}:
        -- ({a,b} ⊆ A.allvars) →
        SH_int A AuSH →
        AuSH.components = (a,b,A_SH) →                                     -- A^SH = ∀a ∃b A_SH(a,b)
        (hA : StarLang.isBase A_SH) →
        (SH_int (¬₁A) (Recreate (b,b,A_SH)))  -- TODO: apagar porque foi batota
        --(SH_int (¬₁A) (Recreate ({f},{a'},(bE₁ a (Term.var a') (¬₁(substitution_formula b ((Term.var f)·(Term.var a)) A_SH))))))      -- TO DO / Problema: problema: o bE₁ devia então aceitar Finset String :'(
        --((SH_int (¬₁A) (V₁ f (E₁ a' (bE₁ a (Term.var (a')) (¬₁(substitution_formula b ((Term.var f)·(Term.var a)) A_SH)))))))         -- (¬A)^SH = ∀f ∃a' [ ∃a∈a' ¬A_SH(a,fa) ]
| unbForall : SH_int A AuSH →
              AuSH.components = (a,b,A_SH) →                                -- A^SH = ∀a ∃b A_SH(a,b)
              --({x,a,b} ⊆ A.allvars) →
              --(SH_int A (V₁ a (E₁ b A_SH))) →                             -- A^SH = ∀a ∃b A_SH(a,b)
              (hA : StarLang.isBase A_SH) →
              (SH_int (V₁ x A) (Recreate (a∪{x},b,A_SH)))                   -- (∀x A)^SH = ∀x,a ∃b [ A_SH(x,a,b) ]
| bForall : SH_int A AuSH →
            AuSH.components = (a,b,A_SH) →                                -- A^SH = ∀a ∃b A_SH(a,b)
            (hA : StarLang.isBase A_SH) →
            (SH_int (bV₁ x t A) (Recreate (a,b,(bV₁ x t A_SH))))
            --({x,a,b} ⊆ A.allvars) →
            --(h : x ∉ t.freevars)
            --(SH_int A (V₁ a (E₁ b A_SH))) →                                 -- A^SH = ∀a ∃b A_SH(a,b)
            --(SH_int (bV₁ x t A) (V₁ a (E₁ b (bV₁ x t A_SH))))               -- (∀x∈t A(x))^SH = ∀a ∃b [ ∀x∈t A_SH(x,a,b) ]

-- TO DO (eu): a tirar este Teste e fazer um melhor
def Teste (a b : String) (f : Term) (A_SH : Formula): Formula := substitution_formula b (f·(Term.var a)) A_SH

-- --------------------------------------------------------------
-- EXAMPLE 2.1 (p.38)
-- Interpretation of (A ∨ (∀x∈t B(x))), with B(x) a base formula.
-- --------------------------------------------------------------

/-
SH_int A AuSH
AuSH.components = (a,b,A_SH)
(hA : StarLang.isBase A_SH)

SH_int B BuSH
BuSH.components = ({},{},B_SH)
(hB : StarLang.isBase B)        -- usar aqui SH_int.base para obter: SH_int B (Recreate ({},{},B))

TO SHOW:
(SH_int ( A ∨₁ (bV₁ x t B) ) (Recreate (a,b,( A_SH ∨₁ (bV₁ x t B_SH) ))))

-/

example
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = ({},{},B_SH)) (hB3 : StarLang.isBase B_SH) :
  (SH_int ( A ∨₁ (bV₁ x t B) ) (Recreate (a,b,( A_SH ∨₁ (bV₁ x t B_SH) )))) :=
  by
    have H := SH_int.base hB3   -- Recreate dá: SH_int B_SH (Recreate (∅, ∅, B_SH))
    -- Mostrar que (bV₁ x t B_SH) isBase
    -- | b_bForall (x : String) (t : Term) (h : isBase A) : isBase (bForall x t A)
    have H2 := StarLang.isBase.b_bForall x t hB3        -- H2 : isBase (bV₁ x t B_SH)
    -- Agora queremos a interpretação do ∨ para termos a interpretação de (A ∨ (∀x∈t B(x)))
    -- Definir a fórmula:
    let F := Formula.bForall x t B_SH
    sorry
    /-
    have H1 : {x} = F.components.1 :=
      by unfold Formula.components
         simp
    have H : (x', t', B_SH') = F.components := by sorry       -- Problema: como garantir que F.components spits the right tuple?
    sorry
    --let cF : Finset String × Finset String × Formula := F.components
    -/

-- ---------------------------------------------------------------------
-- EXAMPLE 2.2 (p.38)                           -- TO DO: depois de termos resolvido a negação do SH_int
-- Interpretation of ∀y∈t ¬(∃x ¬A(x) ∧ B(y)).
-- ---------------------------------------------------------------------

/-
SH_int A AuSH
AuSH.components = (a,b,A_SH)
(hA : StarLang.isBase A_SH)

SH_int B BuSH
BuSH.components = (c,d,B_SH)
(hB : StarLang.isBase B_SH)

TO SHOW:
(SH_int ( bV₁ y t ( ¬₁((E₁ x A)∧₁B) ) ) (Recreate ({x}∪a∪g,b∪(c'),( bV₁ y t (A_SH ∨₁ (bE₁ c c' (substitution_formula d ((Term.var g)·(Term.var c)) B_SH)   )) ))))

example
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (c,d,B_SH)) (hB3 : StarLang.isBase B_SH) :
  (SH_int ( bV₁ y t ( ¬₁((E₁ x A)∧₁B) ) ) (Recreate ({x}∪a∪g,b∪(c'),( bV₁ y t (A_SH ∨₁ (bE₁ c c' (substitution_formula d ((Term.var g)·(Term.var c)) B_SH)   )) )))) := by sorry
-/


-- ---------------------------------------------------------------------
-- REMARK 2.4 (p.40):
-- Interpretation of formulas with empty tuples
-- ---------------------------------------------------------------------

/-
SH_int A AuSH
AuSH.components = (a₁,a₂,A_SH)            -- ∀a ∃b A_SH(a,b)
(hA : StarLang.isBase A_SH)

SH_int B BuSH
BuSH.components = (b₁,{},B_SH)            -- ∀b₁ B_SH(b₁)
(hB : StarLang.isBase B_SH)

SH_int C CuSH
CuSH.components = ({},c₂,C_SH)            -- ∃c₂ A_SH(c₂)
(hC : StarLang.isBase C_SH)
-/

example   -- B∨C
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (b₁,{},B_SH)) (hB3 : StarLang.isBase B_SH)
  (hC1 : SH_int C CuSH) (hC2 : CuSH.components = ({},c₂,C_SH)) (hC3 : StarLang.isBase C_SH) :
  (SH_int ( B∨₁C ) (Recreate (b₁,c₂,(B_SH ∨₁ C_SH)))) := by sorry

example   -- ∀x B(x)
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (b₁,{},B_SH)) (hB3 : StarLang.isBase B_SH)
  (x : String) :
  (SH_int ( V₁ x B ) (Recreate ({x}∪b₁,{},B_SH))) := by sorry

example   -- ∀x∈t C(x)
  (hC1 : SH_int C CuSH) (hC2 : CuSH.components = ({},c₂,C_SH)) (hC3 : StarLang.isBase C_SH)
  (x : String) (t : Term) :
  (SH_int ( bV₁ x t C ) (Recreate ({},c₂,( bV₁ x t C_SH)))) := by sorry

/- Problemma: Não funciona porque b₁ é tipo Finset String mas bE₁ só aceita String
            -> Existe some upward arrow?

lemma EmptyExistentialTuple (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (b₁,{},B_SH)) (hB : StarLang.isBase B_SH) :
  (  SH_int ( ¬₁ B ) ( Recreate ({},{b₁'},( bE₁ b₁ (b₁') (¬₁B_SH) ) ) )  ) := by sorry
-/

lemma EmptyUniversalTuple (hC1 : SH_int C CuSH) (hC2 : CuSH.components = ({},c₂,C_SH)) (hC : StarLang.isBase C_SH) :
  (  SH_int ( ¬₁ C ) ( Recreate (c₂,{},(¬₁ C_SH ) ) )  ) := by sorry



-- ---------------------------------------------------------------------
-- EXAMPLE 2.3 (p.41-42):
-- Interpretation of ∀x∈z ∃y A(x,y) → ∃w ∀x∈z ∃y∈w A(x,y)
-- ---------------------------------------------------------------------

-- TO DO / Problema yes: não consigo ter B = ... (both are formulas)

lemma example_2_3
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = ({},{},A_SH)) (hA3 : StarLang.isBase A_SH)
  (B : Formula) (x y z w : String)
  (H : B = (¬₁( bV₁ x (Term.var z) (¬₁(V₁ y (¬₁ A)))))∨₁(¬₁(V₁ w (¬₁(bV₁ x (Term.var z) (bE₁ y (Term.var w) A)))))) :
  (SH_int B (Recreate ({y'},{w'},( (bV₁ x (Term.var z) (bE₁ y (Term.var y') A)) →₁ (bE₁ w (Term.var w') (bV₁ x (Term.var z) (bE₁ y (Term.var w) A)))  )))) := by sorry



-- ---------------------------------------------------------------------
-- EXAMPLE 2.4 (p.42-43):
-- Interpretation of the bounded axiom of choice
--     ∀x ∃y A_b(x,y) → ∃f ∀x ∃y∈fx A_b(x,y)
-- ---------------------------------------------------------------------

-- TO DO / Problema: não consigo ter B = ... (both are formulas)

lemma int_bAC_ω_star
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = ({},{},A_SH)) (hA3 : StarLang.isBase A_SH)
  (B : Formula) (f x x' y y' a b f f' g Φ: String) :
  --(B = ( (V₁ x (E₁ y A)) →₁ (E₁ f (V₁ x (bE₁ y ((Term.var f)·(Term.var x))) A))) ) ) :
  (SH_int B (Recreate ({g,Φ},{x',f'},(  ( bV₁ x (Term.var x') (bE₁ y ((Term.var g)·(Term.var x)) A) ) →₁ ( bE₁ f (Term.var f')  (bV₁ a ((Term.var Φ)·(Term.var f)) (bE₁ b ((Term.var f)·(Term.var a)) A)) )  )))) := by sorry


-- ---------------------------------------------------------------------
-- PROPOSITION 2.1 (p.43):
-- Interpretation of formulas with defined symbols
-- ---------------------------------------------------------------------

/- EXEMPLO BASE (a tirar depois)
-- -- -- [-- tirar a partir daqui --] -- -- --
example
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (c,d,B_SH)) (hB3 : StarLang.isBase B_SH) :
  (SH_int (  ) (Recreate ( , , ))) := by sorry

(substitution_formula b ((Term.var f)·(Term.var a)) A_SH)
(substitution_formula d ((Term.var g)·(Term.var c)) B_SH)
-- -- -- [-- tirar até aqui --] -- -- --

lemma Int_DefinedSymbols_imp
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (c,d,B_SH)) (hB3 : StarLang.isBase B_SH)
  (f : String):
  (SH_int ( A →₁ B ) (Recreate (f∪c,(a')∪d, ((bV₁ a a' (substitution_formula b ((Term.var f)·(Term.var a)) A_SH)) →₁ B_SH) )) := by sorry

lemma Int_DefinedSymbols_and      -- TO DO: incluir subst no A_SH
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (c,d,B_SH)) (hB3 : StarLang.isBase B_SH)
  (f f' g g' Φ Ψ : String):
  (SH_int ( A ∧₁ B ) (Recreate ({Φ,Ψ},{f',g'}, (bE₁ f (Term.var f') (bE₁ g (Term.var g') ((bV₁ a (((Term.var Φ)·(Term.var f))·(Term.var g)) (substitution_formula b ((Term.var f)·(Term.var a)) A_SH))∧₁(bV₁ c (((Term.var Ψ)·(Term.var f))·(Term.var g)) (substitution_formula d ((Term.var g)·(Term.var c)) B_SH))))) ))) := by sorry

lemma Int_DefinedSymbols_unbExists      -- TO DO: incluir subst no A_SH
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (c,d,B_SH)) (hB3 : StarLang.isBase B_SH)
  (x x' Φ f f': String):
  (SH_int ( E₁ x A ) (Recreate ( {Φ} , {x',f'} , (bE₁ x (Term.var x') (bE₁ f (Term.var f') (bV₁ a (((Term.var Φ)·(Term.var x))·(Term.var f)) (substitution_formula b ((Term.var f)·(Term.var a)) A_SH)))) ))) := by sorry

lemma Int_DefinedSymbols_bExists      -- TO DO: incluir subst no A_SH
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (c,d,B_SH)) (hB3 : StarLang.isBase B_SH)
  (x Φ f f' : String) (t : Term):
  (SH_int ( bE₁ x t A ) (Recreate ( {Φ} , {f'} , (bE₁ f (Term.var f') (bE₁ x t (bV₁ a ((Term.var Φ)·(Term.var f)) (substitution_formula b ((Term.var f)·(Term.var a)) A_SH) ))) ))) := by sorry




Falta: 1. Escrever conclusões: done
       2. Incluir substituições: done
       3. Tentar fazer isTrue para capítulo 3? half done
-/








-- ---------------------------------------------------------------------
-- REMARK 2.6 (p.45):
-- For a given base formula A, the interpretation of ∃x A(x) is given by
--            ∃x' [ ∃x∈x' A(x) ]
-- ---------------------------------------------------------------------

lemma Remark_2_6
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (x x' : String) :
  (SH_int ( E₁ x A ) (Recreate ({},{x'}, (bE₁ x (Term.var x') A) ))) := by sorry


-- ---------------------------------------------------------------------
-- REMARK 2.7 (p.45):
-- Interpretations of formulas of the form ∃x A(x) with empty tuples
-- ---------------------------------------------------------------------

/-
SH_int A AuSH
AuSH.components = (a₁,a₂,A_SH)            -- ∀a ∃b A_SH(a,b)
(hA : StarLang.isBase A_SH)

SH_int B BuSH
BuSH.components = (a,{},B_SH)             -- ∀a B_SH(a)
(hB : StarLang.isBase B_SH)

SH_int C CuSH
CuSH.components = ({},b,C_SH)            -- ∃b C_SH(b)
(hC : StarLang.isBase C_SH)

-- Problema: same as before: a has type Finset String, mas bV₁ aceita String
lemma Remark_2_7_1
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (a,{},B_SH)) (hB3 : StarLang.isBase B_SH)
  (x x' Φ : String) :
  (SH_int ( E₁ x B ) (Recreate ({Φ},{x'}, (bE₁ x (Term.var x') (bV₁ a ((Term.var Φ)·(Term.var x)) B)) ))) := by sorry

-- Problema: same as before: a has type Finset String, mas bE₁ aceita String
lemma Remark_2_7_2
  (hC1 : SH_int C CuSH) (hC2 : BuSH.components = ({},b,C_SH)) (hC3 : StarLang.isBase C_SH)
  (x x' b' : String) :
  (SH_int ( E₁ x C ) (Recreate ({},{x',b}, (bE₁ x (Term.var x') (bE₁ b b' C)) ))) := by sorry
-/


-- ---------------------------------------------------------------------
-- EXAMPLE 2.5 (p.45-46): Example 2.4 revisited
-- Interpretation of the bounded axiom of choice
--     ∀x ∃y A_b(x,y) → ∃f ∀a ∃b∈fa A_b(a,b)
-- ---------------------------------------------------------------------

-- TO DO (eu): copiar enunciado do Example 2.4 para depois prove with previous remarks
