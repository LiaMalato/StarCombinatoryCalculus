import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage
import LeanProjeto2.StarLanguage.Axioms2
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.SHFunctInterp
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

open FOLang
open LFormula
open Term
open Formula
open Set
open Batteries


-- ---------------------------------------------------------------------------------------------------------------
-- ---------------------------------------------------------------------------------------------------------------
--             SECTION 3: THE SOUNDNESS THEOREM AND OTHER RESULTS
-- ---------------------------------------------------------------------------------------------------------------
-- ---------------------------------------------------------------------------------------------------------------

/- EXEMPLO BASE (a tirar depois)
-- -- -- [-- tirar a partir daqui --] -- -- --
example
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (c,d,B_SH)) (hB3 : StarLang.isBase B_SH) :
  (SH_int (  ) (Recreate ( , , ))) := by sorry

(substitution_formula b ((Term.var f)·(Term.var a)) A_SH)
(substitution_formula d ((Term.var g)·(Term.var c)) B_SH)
-- -- -- [-- tirar até aqui --] -- -- --
-/



-- ---------------------------------------------------------------------------------------------------------------
--                     SECTION 3.1: The Soundness theorem
-- ---------------------------------------------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- LEMMA 3.1 (p.48):
-- Monotonicity lemma
-- ---------------------------------------------------------------------

/-
-- Problema / TODO: o ∈₁ e o =₁ também têm de ser para Finset String :(
def inclusion_symbol (x b b' : Finset String) : Formula :=
  (V₁ x ((x ∈₁ b) →₁ (x ∈₁ b')))

notation x "⊆₁" y => inclusion_symbol x y

lemma MonotonicityLemma
  (A : Formula) (b b' : Finset String)
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH) :
  isTrue (((b ⊆₁ b') ∧₁ A_SH) →₁ (substitution_formula b b' A_SH)) := by sorry

-/

-- ---------------------------------------------------------------------
-- THEOREM 3.1 (p.49):
-- Soundness theorem
-- ---------------------------------------------------------------------

-- TO DO: Tem de ser o enunciado geral -> Ref Remark 3.2 (p.49)
-- Problema: Como fazer isTrue com bAC to give A? O que está escrito doesn't work, to prove a conclusão, não precisamos de bAC

/- Problema: same as before com String e Finset String

theorem SoundnessTheorem
  (A : Formula) (t : Term)
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH) :
  (isTrue A) →
  (isTrue.bAC) →
  (isTrue (V₁ a (substitution_formula b (t·(Term.var a)) A_SH))) := by sorry
-/



-- theorem Soundness (A : Formula) : (insert (bAC x y f B) ∅ ⊢ A) → (∃(t:Term), (Provable (∀₁ a A))) := by sorry    -- TBD: falta subst aqui
example {x y f : List String} (A : Formula): (insert (bAC x y f B) ∅ ⊢ A) → (Provable A) := by sorry

lemma interp_b_ac
  (A B:Formula) (x y f g Φ x' f' :List String) (hBase : isBase A)
  (hA1 : SH_int2 A AuSH)
  (hA2 : AuSH.components2 = (a,b,A_SH))
  (hA3 : isBase A_SH) :
  (SH_int2 (bAC x y f B) bACint) → bACint.components2 = (g∪Φ, x'∪f', ((bForallTuple2 x x'.tt (bExistsTuple2 y ((g.tt)⊙(x.tt)) A)) →₁ (bExistsTuple2 f f'.tt (bForallTuple2 a ((Φ.tt)⊙(f.tt)) (bExistsTuple2 b ((f.tt)⊙(a.tt)) A))))) := by sorry



theorem SoundnessTheorem
  (A B : Formula)
  (t : List Term)
  (x y f : List String)

  (hA1 : SH_int2 A AuSH)
  (hA2 : AuSH.components2 = (a,b,A_SH))
  (hA3 : isBase A_SH)
  (hG : Γ₁ = insert (bAC x y f B) Γ)
  (pa : Γ₁ ⊢ A) :
  --(Provable (bAC x y f A)) →
  (Γ₁ ⊢ (∀₁ a (A_SH.subst (HashMap.ofList (b.zip (t⊙(a.tt))))))) := by sorry
    /-
    cases pa
    . -- Ax
      have h1 : A = bAC x y f B := by sorry
      apply ProvableFrom.ax
      sorry
    . -- exMid
      sorry
    . -- subs
      sorry
    . -- exp
      sorry
    . -- contrad
      sorry
    . -- assoc
      sorry
    . -- cut
      sorry
    . -- forallInt
      sorry
    . -- Os axiomas que são universal closures of base formulas
      sorry
    -/

/-
Limpar o que está multiply defined
tt -> eliminar
melhorar ProvableFrom
-/












-- A_SH.subst (HashMap.ofList (b.zip ((f.tt)⊙(a.tt)))))

-- ---------------------------------------------------------------------
-- EXAMPLE 3.1 (p.49-50):
-- Continuation of example 2.3 - Applying the soundness theorem
-- ---------------------------------------------------------------------

-- TO DO (eu): quando example 2.3 estiver bem enunciado


-- ---------------------------------------------------------------------
-- EXAMPLE 3.2 (p.50): The soundness theorem applied to bAC_ω_star
-- Continuation of example 2.4 - Applying the soundness theorem
-- ---------------------------------------------------------------------

-- TO DO (eu): quando example 2.4 estiver bem enunciado


-- ---------------------------------------------------------------------
-- REMARK 3.3 (p.51):
-- Soundness theorem for universal closure of base formulas
-- ---------------------------------------------------------------------




-- ---------------------------------------------------------------------
-- REMARK 3.4 (p.56-57):
-- Typechecking of the types in the soundness theorem
-- ---------------------------------------------------------------------
