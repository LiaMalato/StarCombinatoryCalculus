import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.Axioms2
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.CombinatorialCompleteness
import LeanProjeto2.SHFunctInterp
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Batteries

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
def inclusion_symbol (x b b' : List String) : Formula :=
  (∀₁ x ((x ∈₁ b) →₁ (x ∈₁ b')))

notation b "⊆₁" b' => inclusion_symbol b b'

lemma MonotonicityLemma
  (A : Formula) (b b' : Finset String)
  (intA : SH_int_comp2 A (a,b,A_SH)) (hAbase : isBase A) :
  isTrue (((b ⊆₁ b') ∧₁ A_SH) →₁ ((A_SH).subst (b ⟹ b'.tt))) := by sorry


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
example {x y f a b : List String} (A : Formula): (insert (bAC x y f a b B) ∅ ⊢ A) → (Provable A) := by sorry

/-
lemma interp_b_ac
  (A B:Formula) (x y f g Φ x' f' : String) (hBase : isBase A)
  (hA1 : SH_int_comp A (a,b,A_SH))
  (hA3 : isBase A_SH) :
  SH_int_comp (bAC x y f B) ([g]∪[Φ], [x']∪[f'], ((b∀₁ [x] (var x') (b∃₁ y ((g.tt)⊙(x.tt)) A)) →₁ (b∃₁ f f'.tt (b∀₁ a ((Φ.tt)⊙(f.tt)) (b∃₁ b ((f.tt)⊙(a.tt)) A))))) := by sorry
-/

-- Lemma que diz que o Recreate da interpretação de uma fórmula base é a fórmula base
lemma baseInt_same_as_formInt_b (A:Formula) (hA : isBase A): (SH_int_base_rec A hA) = A := by
  unfold SH_int_base_rec
  simp

#check ((var "x")=₁(var "x"))
#check baseInt_same_as_formInt_b ((var "x")=₁(var "x"))


-- -----------------------------
-- -----------------------------  TBD: alterar SH_int2 para SH_int_comp e mudar a prova
-- -----------------------------
lemma baseInt_same_as_formInt_b2        -- LOL isto já é a definição de Recreate
  (A:Formula) (hA : isBase A)
  (hIntA: SH_int2 A AuSH) (hAcomp: AuSH.components = ([],[],A)): Recreate ([],[],A) = A :=
  by
    simp
    --let H : Formula := Recreate ([],[],A)
    --simp [H]

-- Lemmas que dizem que Rec e Inv são inversos
lemma Rec_Inv_Comp (A:Formula) : Recreate (A.components) = A := by sorry
lemma Comp_Inv_Rec (A:Formula) : (Recreate (a,b,A)).components = (a,b,A) := by sorry

-- Lemma que diz que se uma formula é base que a sua interp é igual a si mesma
lemma baseInt_same_as_formInt
  (A:Formula) (hA : isBase A)
  (hIntA: SH_int2 A AuSH) (hAcomp: AuSH.components = ([],[],A)): AuSH = A :=
  by
    --let H := Recreate (AuSH.components)
    have HH := Rec_Inv_Comp AuSH
    have HHH := baseInt_same_as_formInt_b2 A hA hIntA hAcomp
    rw [← HHH]
    rw [← HH]
    rw [hAcomp]
-- -----------------------------
-- -----------------------------
-- -----------------------------

open Axioms
#check AxiomE1_matrix "x"
#check Axioms.AxiomE1_univ_of_base "x"

-- A interpretação do axioma AxE1 é itself:
#check baseInt_same_as_formInt_b (AxiomE1_matrix "x") (AxiomE1_univ_of_base "x")

--lemma baseAxE1: baseInt_same_as_formInt_b (axiomE1 "x") (AxiomE1_univ_of_base "x") := by sorry
--lemma baseAxE1: SH_int_base_rec ((var "x")=₁(var "x")) (b_atom (isAtomic.at_eq (var "x") (var "x")))  := by sorry

--(SH_int_base_rec ((var x)=₁(var x)) H) = ((var x)=₁(var x))
-- by AxiomE1_univ_of_base



-- Se temos duas interpretações diferentes da mesma formula, então os components são iguais
lemma SH_int_same
  {a b c d : List String} {A A_SH A_SH': Formula}
  (intA : SH_int_comp2 A (a,b,A_SH))
  (intB : SH_int_comp2 A (c,d,A_SH')) :
  a = c ∧ b = d ∧ A_SH = A_SH' :=
    by sorry



-- -------------------------------------------------------
-- -------------------------------------------------------
-- INTERPRETAÇÕES DOS AXIOMAS (dos que NÃO são universal closures de base formulas)
-- -------------------------------------------------------
-- -------------------------------------------------------

lemma AxiomU_int
  (x : String) (t : String) (A : Formula) :
  SH_int_comp2 (AxiomUn x t A) ([t],[],(AxiomUn_matrix x t A)) :=
by
  sorry

/-
def bAC_star_om (x y f a b : String) (A : Formula) : Formula :=
  (∀₁₁ x (∃₁₁ y A)) →₁ (∃₁₁ f (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)))     -- bAC^ω_*
-/




lemma bAC_int
  (x y f a b : String) (A : Formula) (hAbase : isBase A) (y' g a' Φ f' : String):
  SH_int_comp2 (bAC_star_om x y f a b A) ([g]++[Φ],[x']++[f'],
    ((((b∀₁ [x] [var x'] (¬₁((b∀₁ [y] [var y'] (¬₁A)))))).subst ([y']⟹[var g·var x]))) →₁
      (((¬₁(b∀₁ [f] [var f'] (¬₁(b∀₁ [a] [var a'] (¬₁(b∀₁₁ b (var f·var a) (¬₁A))))))).subst
        ([a']⟹[var Φ·var f])))) :=
by
  unfold F_implies
  -- LHS
  have notA := isBase.b_not hAbase
  have intNot1_L := SH_int_comp2.base notA
  have intUnbF1_L := @SH_int_comp2.unbForall (¬₁A) [] [] (¬₁A) [y] intNot1_L
  rw [[y].append_nil] at intUnbF1_L
  have intNot2_L := @SH_int_comp2.neg (∀₁₁ y (¬₁A)) [y] [] (¬₁A) [] [y'] intUnbF1_L
  rw [DoubleNeg] at intNot2_L
  have H_L := Subst_with_empty (b∃₁ [y] [y'].tt A) y
  rw [H_L] at intNot2_L
  have intUnbF2_L := @SH_int_comp2.unbForall (¬₁(∀₁₁ y (¬₁A))) [] [y'] ((b∃₁ [y] [y'].tt A)) [x] intNot2_L
  rw [[x].append_nil] at intUnbF2_L
  have intNot3_L := @SH_int_comp2.neg (∀₁₁ x (¬₁(∀₁₁ y (¬₁A)))) [x] [y'] ((b∃₁ [y] [y'].tt A)) [g] [x'] intUnbF2_L
  -- RHS
  have exA := @bExists_base A b ((var f)·(var a)) hAbase
  have intB := SH_int_comp2.base exA
  have intUnbF1_R := @SH_int_comp2.unbForall (b∃₁₁ b ((var f)·(var a)) A) [] [] (b∃₁₁ b ((var f)·(var a)) A) [a] intB
  rw [[a].append_nil] at intUnbF1_R
  have intNot1_R := @SH_int_comp2.neg (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)) [a] [] (b∃₁₁ b ((var f)·(var a)) A) [] [a'] intUnbF1_R
  have H_R := Subst_with_empty (b∃₁ [a] [a'].tt (b∃₁₁ b (var f·var a) A).not) a
  rw [H_R] at intNot1_R
  have intUnbF2_R := @SH_int_comp2.unbForall (¬₁(∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A))) [] [a'] ((b∃₁ [a] [a'].tt (¬₁(b∃₁₁ b (var f·var a) A)))) [f] intNot1_R
  rw [[f].append_nil] at intUnbF2_R
  have intNot2_R := @SH_int_comp2.neg (∀₁₁ f (¬₁(∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)))) [f] [a'] ((b∃₁ [a] [a'].tt (¬₁(b∃₁₁ b (var f·var a) A)))) [Φ] [f'] intUnbF2_R
  -- All together
  rw [bAC_star_om]
  have intForm := SH_int_comp2.disj intNot3_L intNot2_R
  simp
  rw [bExists, bExistsTuple, bExistsTuple, bExistsTuple, bExistsTuple] at intForm
  rw [DoubleNeg, DoubleNeg, DoubleNeg] at intForm
  exact intForm

-- -------------------------------------------------------
-- INTERPRETAÇÕES DOS AXIOMAS (dos que são universal closures de base formulas)
-- -------------------------------------------------------

-- EQUALITY AXIOMS

lemma AxiomE1_int
  (x : String) :
  SH_int_comp2 (AxiomE1 x) ([x],[],(AxiomE1_matrix x)) :=
by
  have hBase := @AxiomE1_univ_of_base x
  have intBase := SH_int_comp2.base hBase
  have intForm := @SH_int_comp2.unbForall (AxiomE1_matrix x) [] [] (AxiomE1_matrix x) [x] intBase
  rw [[x].append_nil] at intForm
  exact intForm

lemma AxiomE2_int
  (A : Formula) (hAbase : isBase A)
  (x₁ x₂ : String) :
  SH_int_comp2 (AxiomE2 x₁ x₂ A hAbase) ([x₁]++[x₂],[],(AxiomE2_matrix x₁ x₂ A hAbase)) :=
by
  have hBase := @AxiomE2_univ_of_base x₁ x₂ A hAbase
  have intBase := @SH_int_comp2.base (AxiomE2_matrix x₁ x₂ A hAbase) hBase
  have intForall1 := @SH_int_comp2.unbForall (AxiomE2_matrix x₁ x₂ A hAbase) [] [] (AxiomE2_matrix x₁ x₂ A hAbase) [x₂] intBase
  rw [[x₂].append_nil] at intForall1
  have intForall2 := @SH_int_comp2.unbForall (∀₁₁ x₂ (AxiomE2_matrix x₁ x₂ A hAbase)) [x₂] [] (AxiomE2_matrix x₁ x₂ A hAbase) [x₁] intForall1
  exact intForall2

-- COMBINATORY AXIOMS

lemma AxiomC1_int
  (x₁ x₂ : String) :
  SH_int_comp2 (AxiomC1 x₁ x₂) ([x₁]++[x₂],[],(AxiomC1_matrix x₁ x₂)) :=
by
  have hBase := @AxiomC1_univ_of_base x₁ x₂
  have intBase := SH_int_comp2.base hBase
  have intForall1 := @SH_int_comp2.unbForall (AxiomC1_matrix x₁ x₂) [] [] (AxiomC1_matrix x₁ x₂) [x₂] intBase
  rw [[x₂].append_nil] at intForall1
  have intForall2 := @SH_int_comp2.unbForall (∀₁₁ x₂ (AxiomC1_matrix x₁ x₂)) [x₂] [] (AxiomC1_matrix x₁ x₂) [x₁] intForall1
  exact intForall2

lemma AxiomC2_int
  (x₁ x₂ x₃ : String) :
  SH_int_comp2 (AxiomC2 x₁ x₂ x₃) ([x₁]++[x₂]++[x₃],[],(AxiomC2_matrix x₁ x₂ x₃)) :=
by
  have hBase := @AxiomC2_univ_of_base x₁ x₂ x₃
  have intBase := SH_int_comp2.base hBase
  have intForall1 := @SH_int_comp2.unbForall (AxiomC2_matrix x₁ x₂ x₃) [] [] (AxiomC2_matrix x₁ x₂ x₃) [x₃] intBase
  rw [[x₃].append_nil] at intForall1
  have intForall2 := @SH_int_comp2.unbForall (∀₁₁ x₃ (AxiomC2_matrix x₁ x₂ x₃)) [x₃] [] (AxiomC2_matrix x₁ x₂ x₃) [x₂] intForall1
  have intForall3 := @SH_int_comp2.unbForall (∀₁₁ x₂ (∀₁₁ x₃ (AxiomC2_matrix x₁ x₂ x₃))) [x₂ , x₃] [] (AxiomC2_matrix x₁ x₂ x₃) [x₁] intForall2
  exact intForall3

-- PRIMARY AXIOMS

lemma AxiomP1_int
  (x₁ x₂ : String) :
  SH_int_comp2 (AxiomP1 x₁ x₂) ([x₁]++[x₂],[],(AxiomP1_matrix x₁ x₂)) :=
by
  have hBase := @AxiomP1_univ_of_base x₁ x₂
  have intBase := SH_int_comp2.base hBase
  have intForall1 := @SH_int_comp2.unbForall (AxiomP1_matrix x₁ x₂) [] [] (AxiomP1_matrix x₁ x₂) [x₂] intBase
  rw [[x₂].append_nil] at intForall1
  have intForall2 := @SH_int_comp2.unbForall (∀₁₁ x₂ (AxiomP1_matrix x₁ x₂)) [x₂] [] (AxiomP1_matrix x₁ x₂) [x₁] intForall1
  exact intForall2

lemma AxiomS2_int
  (x₁ x₂ x₃ : String) :
  SH_int_comp2 (AxiomS2 x₁ x₂ x₃) ([x₁]++[x₂]++[x₃],[],(AxiomS2_matrix x₁ x₂ x₃)) :=
by
  have hBase := @AxiomS2_univ_of_base x₁ x₂ x₃
  have intBase := SH_int_comp2.base hBase
  have intForall1 := @SH_int_comp2.unbForall (AxiomS2_matrix x₁ x₂ x₃) [] [] (AxiomS2_matrix x₁ x₂ x₃) [x₃] intBase
  rw [[x₃].append_nil] at intForall1
  have intForall2 := @SH_int_comp2.unbForall (∀₁₁ x₃ (AxiomS2_matrix x₁ x₂ x₃)) [x₃] [] (AxiomS2_matrix x₁ x₂ x₃) [x₂] intForall1
  have intForall3 := @SH_int_comp2.unbForall (∀₁₁ x₂ (∀₁₁ x₃ (AxiomS2_matrix x₁ x₂ x₃))) [x₂ , x₃] [] (AxiomS2_matrix x₁ x₂ x₃) [x₁] intForall2
  exact intForall3

-- SECONDARY AXIOMS

lemma AxiomS1_int
  (x₁ x₂ : String) :
  SH_int_comp2 (AxiomS1 x₁ x₂) ([x₁]++[x₂],[],(AxiomS1_matrix x₁ x₂)) :=
by
  have hBase := @AxiomS1_univ_of_base x₁ x₂
  have intBase := SH_int_comp2.base hBase
  have intForall1 := @SH_int_comp2.unbForall (AxiomS1_matrix x₁ x₂) [] [] (AxiomS1_matrix x₁ x₂) [x₂] intBase
  rw [[x₂].append_nil] at intForall1
  have intForall2 := @SH_int_comp2.unbForall (∀₁₁ x₂ (AxiomS1_matrix x₁ x₂)) [x₂] [] (AxiomS1_matrix x₁ x₂) [x₁] intForall1
  exact intForall2

lemma AxiomP2_int
  (x₁ x₂ x₃ : String) :
  SH_int_comp2 (AxiomP2 x₁ x₂ x₃) ([x₁]++[x₂]++[x₃],[],(AxiomP2_matrix x₁ x₂ x₃)) :=
by
  have hBase := @AxiomP2_univ_of_base x₁ x₂ x₃
  have intBase := SH_int_comp2.base hBase
  have intForall1 := @SH_int_comp2.unbForall (AxiomP2_matrix x₁ x₂ x₃) [] [] (AxiomP2_matrix x₁ x₂ x₃) [x₃] intBase
  rw [[x₃].append_nil] at intForall1
  have intForall2 := @SH_int_comp2.unbForall (∀₁₁ x₃ (AxiomP2_matrix x₁ x₂ x₃)) [x₃] [] (AxiomP2_matrix x₁ x₂ x₃) [x₂] intForall1
  have intForall3 := @SH_int_comp2.unbForall (∀₁₁ x₂ (∀₁₁ x₃ (AxiomP2_matrix x₁ x₂ x₃))) [x₂ , x₃] [] (AxiomP2_matrix x₁ x₂ x₃) [x₁] intForall2
  exact intForall3

lemma AxiomS3_int
  (x₁ x₂ x₃ y : String) :
  SH_int_comp2 (AxiomS3 x₁ x₂ x₃ y) ([x₁]++[x₂]++[x₃],[],(AxiomS3_matrix x₁ x₂ x₃ y)) :=
by
  have hBase := @AxiomS3_univ_of_base x₁ x₂ x₃ y
  have intBase := SH_int_comp2.base hBase
  have intForall1 := @SH_int_comp2.unbForall (AxiomS3_matrix x₁ x₂ x₃ y) [] [] (AxiomS3_matrix x₁ x₂ x₃ y) [x₃] intBase
  rw [[x₃].append_nil] at intForall1
  have intForall2 := @SH_int_comp2.unbForall (∀₁₁ x₃ (AxiomS3_matrix x₁ x₂ x₃ y)) [x₃] [] (AxiomS3_matrix x₁ x₂ x₃ y) [x₂] intForall1
  have intForall3 := @SH_int_comp2.unbForall (∀₁₁ x₂ (∀₁₁ x₃ (AxiomS3_matrix x₁ x₂ x₃ y))) [x₂ , x₃] [] (AxiomS3_matrix x₁ x₂ x₃ y) [x₁] intForall2
  exact intForall3

lemma AxiomS4_int
  (x₁ x₂ : String) :
  SH_int_comp2 (AxiomS4 x₁ x₂) ([x₁],[],(AxiomS4_matrix x₁ x₂)) :=
by
  have hBase := @AxiomS4_univ_of_base x₁ x₂
  have intBase := SH_int_comp2.base hBase
  have intForm := @SH_int_comp2.unbForall (AxiomS4_matrix x₁ x₂) [] [] (AxiomS4_matrix x₁ x₂) [x₁] intBase
  rw [[x₁].append_nil] at intForm
  exact intForm


-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------


-- lemma que podemos mudar os nomes das variáveis dos quantificadores
def SH_int_comp_renaming
  (A : Formula) {A_SH : Formula} (a b c d : List String) :=
  (SH_int_comp2 A (a,b,A_SH)) → (SH_int_comp2 A (c,d,A_SH))
  -- SH_int_comp A (a,b,A_SH) =

def SH_int_comp_renaming2
  (A : Formula) {intA : SH_int_comp2 A (a,b,A_SH)} (c d : List String) :=
  SH_int_comp2 A (a,b,A_SH) = (SH_int_comp2 A (c,d,A_SH))

lemma SH_int_comp_renaming_lemma
  (a b c d : List String) (A A_SH: Formula) (intA : SH_int_comp2 A (a,b,A_SH)) :
  (SH_int_comp2 A (c,d,A_SH)) := by sorry

open Axioms


-- -------------------------------------------------------
-- INTERPRETAÇÕES DOS AXIOMAS DO CALCULO DE SHOENFIELD
-- -------------------------------------------------------

-- INTERPRETAÇÕES DO SHOENFIELD CALCULUS:

-- 1. Excluded Middle (axiom): A∨(¬A)

def FormExMid (A: Formula) := (¬₁A)∨₁A
def FormExMid_matrix (A A_SH : Formula) (a b f a' : List String) := (((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))∨₁A_SH)

lemma intExMid
  (A A_SH: Formula) (intA2: SH_int_comp2 A (a,b,A_SH))
  (α β f a' : List String):
  SH_int_comp2 (FormExMid A) (f++α,a'++β,(FormExMid_matrix A A_SH a b f a')) :=
by
  have intA1 := SH_int_comp_renaming_lemma a b α β A A_SH intA2
  have intA2not := @SH_int_comp2.neg A a b A_SH f a' intA2
  exact SH_int_comp2.disj intA2not intA1

lemma intExMid2
  (A A_SH: Formula) (intA2: SH_int_comp2 A (a,b,A_SH))
  (α β f a' : List String):
  SH_int_comp2 (FormExMid A) (f++α,a'++β,(((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)) ∨₁ A_SH)) :=
by
  have intA1 := SH_int_comp_renaming_lemma a b α β A A_SH intA2
  have intA2not := @SH_int_comp2.neg A a b A_SH f a' intA2
  --rw [FormExMid]
  --have H := SH_int_comp2.disj intA1 intA2not
  --exact H
  exact SH_int_comp2.disj intA2not intA1

-- intExMid A A_SH intA α β f a'

-- 2. Substitution (axiom)

-- 3. Expansion (inference rule)

-- 4. Contraction (inference rule)

example
  (A : Formula) (intA: SH_int_comp2 A (a,b,A_SH))
  (α β : List String):
  SH_int_comp2 (A∨₁A) (a++α,b++β,(A_SH ∨₁ A_SH)) :=
by
  have intA' := SH_int_comp_renaming_lemma a b α β A A_SH intA
  exact SH_int_comp2.disj intA intA'

-- 5. Associativity (inference rule)

lemma InfRule_Assoc1
  (A B C: Formula)
  (intA: SH_int_comp2 A (a,b,A_SH)) (intB: SH_int_comp2 B (c,d,B_SH)) (intC: SH_int_comp2 C (u,v,C_SH)):
  SH_int_comp2 (A∨₁(B∨₁C)) (a++c++u,b++d++v,(A_SH ∨₁ (B_SH ∨₁ C_SH))) :=
by
  have intOr1 := SH_int_comp2.disj intB intC
  have intOr2 := SH_int_comp2.disj intA intOr1
  rw [List.append_assoc a c u, List.append_assoc b d v]
  exact intOr2

lemma InfRule_Assoc2
  (A B C: Formula)
  (intA: SH_int_comp2 A (a,b,A_SH)) (intB: SH_int_comp2 B (c,d,B_SH)) (intC: SH_int_comp2 C (u,v,C_SH)):
  SH_int_comp2 ((A∨₁B)∨₁C) (a++c++u,b++d++v,((A_SH ∨₁ B_SH) ∨₁ C_SH)) :=
by
  have intOr1 := SH_int_comp2.disj intA intB
  have intOr2 := SH_int_comp2.disj intOr1 intC
  exact intOr2



-- 6. Cut (inference rule)

-- 7. Forall introduction (inference rule)























-- ----------------------------------------------------
-- ----------------------------------------------------

/-
DEFINITIONS TO GET ACCESS TO THE INTERPRETATIONS OF THE AXIOMS
AND THE INFERENCE RULES OF SHOENFIELD'S CALCULUS
-/

def intExMid_Form (A A_SH: Formula) (a b α β f a' : List String) :=
  (SH_int_comp2 ((¬₁A)∨₁A) (f++α,a'++β,(((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))∨₁A_SH)))

def intExMid_matrix (A_SH: Formula) (a b f a' : List String) :=
  (((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))∨₁A_SH)

-- intExMid_matrix A_SH a b f a'

lemma intExMid_Form_lemma (A A_SH: Formula) (a b α β f a' : List String) :
  (SH_int_comp2 ((¬₁A)∨₁A) (f++α,a'++β,(((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))∨₁A_SH))) := by sorry

/-
theorem SoundnessTheorem_exMid
  (A A_SH: Formula)
  (a a₁ a₂ b b₁ b₂ f a' α β x y g: List String)
  (pa : Γ₁ ⊢ (FormExMid A))
  (hG : Γ₁ = insert (bAC x y g c d B) Γ)
  (intA : SH_int_comp2 A (a, b, A_SH))
  (intA' : SH_int_comp2 A (α, β, A_SH))         -- TENTAR JA COM ISTO I GUESS
  (intA2 : (SH_int_comp2 (FormExMid A) (α++f,β++a',(intExMid_matrix A_SH a b f a')))))
  :
  --(Provable (bAC x y f A)) →
  ∃(t:List Term), (Γ ⊢ (∀₁ α++f ((((A_SH ∨₁ ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))))).subst ))) := by sorry
-/

def interp_incomp (A : Formula) {a b : List String} {A_SH : Formula}:= (SH_int_comp A (a,b,A_SH))

open lambda
#eval ((la "x" Π₁).to_term)
-- (la f (la a (𝔰₁·a))).to_term     --> TBD: la precisa de aceitar tuplos :(

theorem SoundnessTheorem2
  (A B : Formula)
  --(t : List Term)
  (x y g : String)
  (a a₁ a₂ α b b₁ b₂ β f a' : List String)
  --(c d : List String)
  (pa : Γ₁ ⊢ A)
  (hG : Γ₁ = insert (bAC_star_om x y g c d B) Γ)
  (intA : SH_int_comp2 A (a₁,b₁,A_SH))
  --(hA2 : AuSH.components = (a,b,A_SH))
  --(hA3 : isBase A_SH)
  :
  --(Provable (bAC x y f A)) →
  ∃a b A_SH,
  SH_int_comp2 A (a,b,A_SH) ∧
  ∃(t:List Term), (Γ ⊢ (∀₁ a (A_SH.subst (HashMap.ofList (b.zip (t⊙(a.tt))))))) :=
by
  cases pa
  . sorry
  . rename_i A
    have Coisa := intExMid_Form_lemma A A_SH a b α β f a'
    use f ++ α, a' ++ β, (((b∃₁ a a'.tt A_SH.not).subst (b⟹f.tt⊙a.tt)).or A_SH)
    constructor
    . exact Coisa
    . let p := fun (x y : List String) => ([𝔰₁])⊙(y.tt)   -- This is wrong, mas é para termos uma ideia
      let q := fun (x y : List String) => (y.tt)⊙(x.tt)   -- This is wrong, mas é para termos uma ideia
      --let p'⊙((f++a).tt) :=
      -- (b ⟹ ((f.tt)⊙(a.tt)))
      --use (p)∪(q)
      sorry
    /-
    use []
        simp [HashMap.ofList]
        --unfold AxiomE1_matrix unbForallTuple
        --simp [List.foldr]
        apply AxE₁



    def intExMid_Form (A A_SH: Formula) (a b α β f a' : List String) :=
    (SH_int_comp2 ((¬₁A)∨₁A) (f++α,a'++β,(((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))∨₁A_SH)))
    -/

    --have a, (a₂++a'), (A_SH ∨₁ ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)))
    --  ∨₁ ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))
    -- intExMid A A_SH intA a₁ b₁ f a'
    --use a₁++f, b₁++a', (intExMid A A_SH intA a₁ b₁ f a')
    --have ren (α β : List String) := SH_int_comp_renaming_lemma a₁ b₁ α β A A_SH intA
    --use [z], [], (AxiomE1_matrix z)
    /-
    SH_int_comp2 (A∨₁(¬₁A)) (α++f,β++a',(A_SH ∨₁ ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))))
    SH_int_comp2 (A∨₁(¬₁A)) (a₁++f,b₁++a',(A_SH ∨₁ ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))))

    lemma intExMid
    (A A_SH: Formula) (intA2: SH_int_comp2 A (a,b,A_SH))
    (α β f a' : List String):
    SH_int_comp2 (A∨₁(¬₁A)) (α++f,β++a',(A_SH ∨₁ ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)))) :=
    -/
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . -- repeat {} OU acrescentar lema
    rename_i z
    --rcases H with ⟨ _ , _ , (AxiomE1_matrix), H2 ⟩
    sorry
    --(AxiomE1_matrix z)
    --use [z], [], (AxiomE1_matrix z)
    --have intAxE1 := AxiomE1_int z
    --constructor
    --. exact intAxE1
    --. use []
    --  simp [HashMap.ofList]
      --unfold AxiomE1_matrix unbForallTuple
      --simp [List.foldr]
    --  apply AxE₁
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry


lemma all_formulas_have_an_intepretation {f a' : List String}:
  ∀ A, ∃ a b A_SH, SH_int_comp2 A (a, b, A_SH) :=
by
  intro A
  induction A with
  | L_Form A_L =>
      induction A_L with
      | atomic_L R ts => sorry
      | not_L A intA => sorry
      | or_L A B intA intB => sorry
      | forall_L x A intA =>
          cases intA; rename_i a intA
          cases intA; rename_i b intA
          cases intA; rename_i A_SH intA
          sorry
  | rel R ts =>
      have hAt : isAtomic (rel R ts) := by exact isAtomic.at_rel
      have hBase : isBase (rel R ts) := by exact isBase.b_atom hAt
      have intBase := SH_int_comp2.base hBase
      existsi []; existsi []; existsi (rel R ts)
      exact intBase
  | eq t₁ t₂ =>
      have hAt : isAtomic (t₁=₁t₂) := by exact isAtomic.at_eq t₁ t₂
      have hBase : isBase (t₁=₁t₂) := by exact isBase.b_atom hAt
      have intBase := SH_int_comp2.base hBase
      existsi []; existsi []; existsi (t₁=₁t₂)
      exact intBase
  | mem t₁ t₂ =>
      have hAt : isAtomic (t₁∈₁t₂) := by exact isAtomic.at_mem t₁ t₂
      have hBase : isBase (t₁∈₁t₂) := by exact isBase.b_atom hAt
      have intBase := SH_int_comp2.base hBase
      existsi []; existsi []; existsi (t₁∈₁t₂)
      exact intBase
  | not A intA =>
      cases intA; rename_i a intA
      cases intA; rename_i b intA
      cases intA; rename_i A_SH intA
      existsi f; existsi a'; existsi ((b∃₁ a a'.tt A_SH.not).subst (b⟹f.tt⊙a.tt))
      apply SH_int_comp2.neg
      exact intA
  | or A B intA intB =>
      cases intA; rename_i a intA
      cases intA; rename_i b intA
      cases intA; rename_i A_SH intA
      cases intB; rename_i c intB
      cases intB; rename_i d intB
      cases intB; rename_i B_SH intB
      existsi a++c; existsi b++d; existsi (A_SH ∨₁ B_SH)
      apply SH_int_comp2.disj
      . apply intA
      . apply intB
  | unbForall x A intA =>
      cases intA; rename_i a intA
      cases intA; rename_i b intA
      cases intA; rename_i A_SH intA
      existsi [x]++a; existsi b; existsi A_SH
      have H := @SH_int_comp2.unbForall A a b A_SH [x] intA
      exact H
  | bForall x t A intA =>
      cases intA; rename_i a intA
      cases intA; rename_i b intA
      cases intA; rename_i A_SH intA
      existsi a; existsi b; existsi (b∀₁₁ x t A_SH)
      have H := @SH_int_comp2.bForall A a b A_SH [x] [t] intA
      exact H






theorem SoundnessTheorem
  (A B : Formula)
  --(t : List Term)
  (x y f a' : List String)
  (pa : Γ₁ ⊢ A)
  (hG : Γ₁ = insert (bAC x y f c d B) Γ)
  --(hA2 : AuSH.components = (a,b,A_SH))
  --(hA3 : isBase A_SH)
   :
  --(Provable (bAC x y f A)) →
  ∃a b A_SH,
  SH_int_comp2 A (a,b,A_SH) ∧
  ∃(t:List Term), (Γ ⊢ (∀₁ a (A_SH.subst (HashMap.ofList (b.zip (t⊙(a.tt))))))) := by
    cases pa
    . -- Ax
      rename_i AinΓ
      have h1 : A = bAC x y f c d B := by sorry
      --apply ProvableFrom.ax
      sorry
    . -- exMid
      rename_i A
      have hx := @all_formulas_have_an_intepretation f a' A
      cases hx
      rename_i a hxx
      cases hxx
      rename_i b hxxx
      cases hxxx
      rename_i A_SH A_interp
      sorry
      /-
      SH_int_comp2 (A∨₁(¬₁A)) (α++f,β++a',(A_SH ∨₁ ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))))
      -/
      /-
      rename_i A
      have intExMid
      --have H := SH_int_comp_renaming_lemma a b α β A A_SH intA
      let α := List String
      let β := List String
      let g := List String
      let a' := List String
      let z := String
      sorry
      --use [z], [], (AxiomE1_matrix z)
      --use [α++f], (β++a'), (A_SH ∨₁ ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)))
      -/
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
      rename_i B h
      rename_i D z A
      sorry
  -- Os axiomas que são universal closures of base formulas
    . -- repeat {} OU acrescentar lema
      rename_i z
      use [z], [], (AxiomE1_matrix z)
      have intAxE1 := AxiomE1_int z
      constructor
      . exact intAxE1
      . use []
        simp [HashMap.ofList]
        --unfold AxiomE1_matrix unbForallTuple
        --simp [List.foldr]
        apply AxE₁
    . -- Os axiomas que são universal closures of base formulas
      rename_i x₁ x₂ A hAbase
      use [x₁, x₂], [], (AxiomE2_matrix x₁ x₂ A hAbase)
      have intAxE2 := AxiomE2_int A hAbase x₁ x₂
      constructor
      . exact intAxE2
      . use []
        --simp [HashMap.ofList]
        --apply AxE₂
        sorry
        --unfold AxiomE2_matrix unbForallTuple
    . sorry   -- é o AxU -> falta interp de AxU
    . rename_i x₁ x₂
      use [x₁, x₂], [], (AxiomC1_matrix x₁ x₂)
      have intAxC1 := AxiomC1_int x₁ x₂
      constructor
      . exact intAxC1
      . use []
        simp [HashMap.ofList]
        apply AxC₁
    . rename_i x₁ x₂ x₃
      use [x₁, x₂, x₃], [], (AxiomC2_matrix x₁ x₂ x₃)
      have intAxC2 := AxiomC2_int x₁ x₂ x₃
      constructor
      . exact intAxC2
      . use []
        simp [HashMap.ofList]
        apply AxC₂
    . rename_i x₁ x₂
      use [x₁, x₂], [], (AxiomP1_matrix x₁ x₂)
      have intAxP1 := AxiomP1_int x₁ x₂
      constructor
      . exact intAxP1
      . use []
        simp [HashMap.ofList]
        apply AxP₁
    . rename_i x₁ x₂ x₃
      use [x₁, x₂, x₃], [], (AxiomP2_matrix x₁ x₂ x₃)
      have intAxP2 := AxiomP2_int x₁ x₂ x₃
      constructor
      . exact intAxP2
      . use []
        simp [HashMap.ofList]
        apply AxP₂
    . rename_i x₁ x₂
      use [x₁, x₂], [], (AxiomS1_matrix x₁ x₂)
      have intAxS1 := AxiomS1_int x₁ x₂
      constructor
      . exact intAxS1
      . use []
        simp [HashMap.ofList]
        apply AxS₁
    . rename_i x₁ x₂ x₃
      use [x₁, x₂, x₃], [], (AxiomS2_matrix x₁ x₂ x₃)
      have intAxS2 := AxiomS2_int x₁ x₂ x₃
      constructor
      . exact intAxS2
      . use []
        simp [HashMap.ofList]
        apply AxS₂
    . rename_i x₁ x₂ x₃ y
      use [x₁, x₂, x₃], [], (AxiomS3_matrix x₁ x₂ x₃ y)
      have intAxS3 := AxiomS3_int x₁ x₂ x₃ y
      constructor
      . exact intAxS3
      . use []
        simp [HashMap.ofList]
        apply AxS₃
    . rename_i x₁ x₂
      use [x₁], [], (AxiomS4_matrix x₁ x₂)
      have intAxS4 := AxiomS4_int x₁ x₂
      constructor
      . exact intAxS4
      . use []
        simp [HashMap.ofList]
        apply AxS₄

/-
Limpar o que está multiply defined
melhorar ProvableFrom
-/



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









-- -------------------------------------------------------

-- INTERPRETAÇÕES DOS AXIOMAS (que não são univ closures de base formulas): AxU e bAC

-- AxU



-- bAC

lemma bAC_PrimSymb
  (A : Formula) (x y f a b : String) :
  ((∀₁₁ x (∃₁₁ y A)) →₁ (∃₁₁ f (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)))) = ((¬₁ (∀₁₁ x (¬₁(∀₁₁ y (¬₁A))))) ∨₁ (¬₁ (∀₁₁ f (¬₁ (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)))))) :=
by
  simp
  --unfold F_implies
  --unfold unbExists
  --rfl

lemma bAC_star_om_PrimSymb
  (A : Formula) (x y f a b : String) :
  (bAC_star_om x y f a b A) = ((¬₁ (∀₁₁ x (¬₁(∀₁₁ y (¬₁A))))) ∨₁ (¬₁ (∀₁₁ f (¬₁ (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)))))) :=
by
  unfold bAC_star_om
  simp

/-
def bAC_star_om (x y f a b : List String) (A : Formula) : Formula := (∀₁ x (∃₁ y A)) →₁ (∃₁ f (∀₁ a (b∃₁ b ((f.tt)⊙(a.tt)) A)))     -- bAC^ω_*
def bAC_star_om (x y f a b : String) (A : Formula) : Formula := (∀₁₁ x (∃₁₁ y A)) →₁ (∃₁₁ f (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)))     -- bAC^ω_*

-/

example
  (A : Formula) (hAbase : isBase A) (x x' y f f' a b g Φ : String):
  SH_int_comp2 (bAC_star_om x y f a b A) ([g]++[Φ],[x']++[f'],(A)) :=
by sorry
  --have intOr1 := SH_int_comp.disj intB intC
  --have intOr2 := SH_int_comp.disj intA intOr1
  --rw [List.append_assoc a c u, List.append_assoc b d v]
  --exact intOr2

/-
FALTA SUBST
(b∀₁₁ x (var x') (b∃₁₁ y ((var g)·(var x)) A)) →₁ (b∃₁₁ f (var f') (b∀₁₁ a ((var Φ)·(var f)) (b∃₁₁ b ((var f)·(var a)) A)))

Com subst: ⟹
(b∀₁₁ x (var x') (b∃₁ [y] (A.subst ([y'] ⟹ ([(var g)·(var x)])))) A)) →₁ (b∃₁₁ f (var f') (b∀₁ a (A.subst ([a'] ⟹ ([(var Φ)·(var f)]))) (b∃₁₁ b ((var f)·(var a)) A)))
-/




/-
lemma AxiomS4_int
  (x₁ x₂ : String)
  (hAxS4: axiomS4_matrix x₁ x₂) :
  SH_int_comp (AxiomS4_matrix x₁ x₂) (x₁,[],(axiomS4_matrix x₁ x₂))) := by sorry

SH_int_comp A (a,b,A_SH)) :

example
  (A B : Formula)
  (hA: SH_int_comp A (a,b,A_SH)) (hB : isBase B) :
  SH_int_comp (A ∨₁ (b∀₁ [x] t B)) (a,b,(A_SH ∨₁ (b∀₁ [x] t B))) :=
-/
