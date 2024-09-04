import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.Axioms2
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.SHFunctInterp
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

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

-- Lemma que diz que o Recreate da interpretação de uma fórmula base é a fórmula base
lemma baseInt_same_as_formInt_b (A:Formula) (hA : isBase A): (SH_int_base_rec A hA) = A := by
  unfold SH_int_base_rec
  simp

#check ((var "x")=₁(var "x"))
#check baseInt_same_as_formInt_b ((var "x")=₁(var "x"))


lemma baseInt_same_as_formInt_b2        -- LOL isto já é a definição de RecreateEmpty
  (A:Formula) (hA : isBase A)
  (hIntA: SH_int2 A AuSH) (hAcomp: AuSH.components5 = ([],[],A)): RecreateEmpty ([],[],A) = A :=
  by
    simp
    --let H : Formula := RecreateEmpty ([],[],A)
    --simp [H]

-- Lemmas que dizem que Rec e Inv são inversos
lemma Rec_Inv_Comp (A:Formula) : RecreateEmpty (A.components5) = A := by sorry
lemma Comp_Inv_Rec (A:Formula) : (RecreateEmpty (a,b,A)).components5 = (a,b,A) := by sorry

-- Lemma que diz que se uma formula é base que a sua interp é igual a si mesma
lemma baseInt_same_as_formInt
  (A:Formula) (hA : isBase A)
  (hIntA: SH_int2 A AuSH) (hAcomp: AuSH.components5 = ([],[],A)): AuSH = A :=
  by
    --let H := RecreateEmpty (AuSH.components5)
    have HH := Rec_Inv_Comp AuSH
    have HHH := baseInt_same_as_formInt_b2 A hA hIntA hAcomp
    rw [← HHH]
    rw [← HH]
    rw [hAcomp]



open Axioms
#check axiomE1 "x"
#check Axioms.AxiomE1_univ_of_base "x"

-- A interpretação do axioma AxE1 é itself:
#check baseInt_same_as_formInt_b (axiomE1 "x") (AxiomE1_univ_of_base "x")

--lemma baseAxE1: baseInt_same_as_formInt_b (axiomE1 "x") (AxiomE1_univ_of_base "x") := by sorry
--lemma baseAxE1: SH_int_base_rec ((var "x")=₁(var "x")) (b_atom (isAtomic.at_eq (var "x") (var "x")))  := by sorry

--(SH_int_base_rec ((var x)=₁(var x)) H) = ((var x)=₁(var x))
-- by AxiomE1_univ_of_base


lemma Formula.subst_empty (A: Formula) : A.subst HashMap.empty = A := by sorry


theorem SoundnessTheorem
  (A B : Formula)
  --(t : List Term)
  (x y f : List String)

  (hA1 : SH_int_comp A (a,b,A_SH))
  --(hA2 : AuSH.components5 = (a,b,A_SH))
  --(hA3 : isBase A_SH)
  (hG : Γ₁ = insert (bAC x y f B) Γ)
  (pa : Γ₁ ⊢ A) :
  --(Provable (bAC x y f A)) →
  ∃(t:List Term), (Γ ⊢ (∀₁ a (A_SH.subst (HashMap.ofList (b.zip (t⊙(a.tt))))))) := by --sorry
    cases pa
    . -- Ax
      rename_i AinΓ
      have h1 : A = bAC x y f B := by sorry
      --apply ProvableFrom.ax
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
      -- repeat {} OU acrescentar lema
      rename_i z
      let H := isBase (AxiomE1 z)
      use []
      simp [HashMap.ofList]
      rw [Formula.subst_empty]
      -- acrescentar interp do axioma
      -- apply lemma para quantificadores ficarem vazios




      sorry
    . sorry
    . sorry
    . sorry
    . sorry
    . sorry
    . sorry
    . sorry
    . sorry
    . sorry
    . rename_i x₁ x₂
      sorry

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
