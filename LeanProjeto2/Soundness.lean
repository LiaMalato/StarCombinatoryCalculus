import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.Axioms
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

def inclusion_symbol {x : List String } (b b' : List String) : Formula :=
  (∀₁ x ((x.tt ∈_t b.tt) →₁ (x.tt ∈_t b'.tt)))

notation b "⊆₁" b' => inclusion_symbol b b'


/-
lemma MonotonicityLemma
  (A : Formula) (b b' : List String)
  (intA : SH_int_comp2 A (a,b,A_SH)) (hAbase : isBase A) :
  Γ ⊢ (((b ⊆₁ b') ∧₁ A_SH) →₁ ((A_SH).subst (b ⟹ b'.tt))) := by sorry
-/


/-
-- Problema / TODO: o ∈₁ e o =₁ também têm de ser para Finset String :(
def inclusion_symbol (x b b' : List String) : Formula :=
  (∀₁ x.tt ((x.tt ∈_t b.tt) →₁ (x.tt ∈_t b'.tt)))

∈_t

notation b "⊆₁" b' => inclusion_symbol b b'

lemma MonotonicityLemma
  (A : Formula) (b b' : List String)
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

open axioms
#check AxiomE1_matrix "x"
#check axioms.AxiomE1_univ_of_base "x"

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

-- Intepretação do axiom AxU
lemma AxiomU_int
  (x : String) (t : String) (A : Formula) :
  SH_int_comp2 (AxiomUn x t A) ([t],[],(AxiomUn_matrix x t A)) :=
by
  sorry

/-
def bAC_star_om (x y f a b : String) (A : Formula) : Formula :=
  (∀₁₁ x (∃₁₁ y A)) →₁ (∃₁₁ f (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)))     -- bAC^ω_*
-/

-- Interpretação do bounded axiom of choice bAC

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
-- def SH_int_comp_renaming
--   (A : Formula) {A_SH : Formula} (a b c d : List String) :=
--   (SH_int_comp2 A (a,b,A_SH)) → (SH_int_comp2 A (c,d,A_SH))
--   -- SH_int_comp A (a,b,A_SH) =

-- def SH_int_comp_renaming2
--   (A : Formula) {intA : SH_int_comp2 A (a,b,A_SH)} (c d : List String) :=
--   SH_int_comp2 A (a,b,A_SH) = (SH_int_comp2 A (c,d,A_SH))

lemma SH_renaming2                  -- NOVO (25 set)
   (a b c d : List String) (A A_SH: Formula)
   (intA : SH_int_comp2 A (a,b,A_SH)) :
   (SH_int_comp2 A (c,d,((A_SH.subst (a⟹c.tt)).subst (b⟹d.tt)))) := by sorry


-- #check SH_int_comp2 (∀₁₁ "x" (.rel "r" [Term.var "x", Term.var "y"]))
--                     (["x"], [], (.rel "r" [Term.var "x", Term.var "y"]))


/-
(¬₁A_SH)).subst (b⟹f.tt⊙a.tt)
-/

open axioms

-- -------------------------------------------------------
-- HELPER FUNCTIONS
-- -------------------------------------------------------

lemma subst_at_a_time
  (A: Formula) (x: String) (t:Term):
  A.subst (HashMap.ofList ((x, t) :: hm)) = (A.subst (HashMap.ofList [(x, t)])).subst (HashMap.ofList hm):= by sorry

lemma subst_useless
  (A: Formula) :
  A.subst (HashMap.ofList [(x, .var x)]) = A := by sorry


lemma helper2 (A: Formula) (a:List String) :
  A.subst (a⟹(List.map var a)) = A :=
by
  induction a generalizing A
  case nil =>
    simp
    rw [HashMap.ofList, List.foldl]
    simp
  case cons h tl ih =>
    simp [List.map, with_t]
    rw [subst_at_a_time]
    have ih_sp := ih (A.subst (HashMap.ofList [(h, var h)]))
    rw [with_t] at ih_sp
    simp [subst_useless] at ih_sp
    simp [subst_useless]
    exact ih_sp

-- Renaming variables in an intepretation
lemma SH_ren (A A_SH: Formula) (intA2: SH_int_comp2 A (a,b,A_SH)) :
    ∃α, ∃β,
    SH_int_comp2 A (α, β, (A_SH.subst (a ⟹ α.tt)).subst (b ⟹ β.tt)) :=
by
    use a
    use b
    simp
    rw[←with_t, ←with_t]
    rw [helper2 A_SH a, helper2 A_SH b]
    assumption

-- Interpretações de uma mesma fórmula são equivalentes
lemma SH_equiv (A A_SH A_'SH: Formula) (a b a' b' : List String) (h1 : SH_int_comp2 A (a,b,A_SH)) (h2 : SH_int_comp2 A (a',b',A'_SH)):
  (SH_int_comp2 A (a,b,A_SH)) ↔ (SH_int_comp2 A (a',b',A'_SH)) := by sorry

-- Interpretações de uma mesma fórmula são equivalentes e as componentes também
lemma SH_equiv_comp (A A_SH A_'SH: Formula) (a b a' b' : List String) (h1 : SH_int_comp2 A (a,b,A_SH)) (h2 : SH_int_comp2 A (a',b',A'_SH)):
  (a=a') ∧ (b=b') ∧ (A_SH = A'_SH) := by sorry

-- Se uma mesma fórmula tem dois α-renamings a partir das mesmas variáveis, então as interpretações são as mesmas
lemma helper_cancel_int
  (A A_SH: Formula)
  (intA : SH_int_comp2 A (a,b,A_SH))
  (intA1: SH_int_comp2 A (a₁,b₁,(A_SH.subst (a ⟹ a₁.tt)).subst (b ⟹ b₁.tt)))
  (intA2: SH_int_comp2 A (a₂,b₂,(A_SH.subst (a ⟹ a₂.tt)).subst (b ⟹ b₂.tt))) :
  (a₁,b₁,(A_SH.subst (a ⟹ a₁.tt)).subst (b ⟹ b₁.tt)) = (a₂,b₂,(A_SH.subst (a₁ ⟹ a₂.tt)).subst (b₁ ⟹ b₂.tt)) := by sorry

lemma helper_intro_int
  (A A_SH: Formula) --(a b α β : List String)
  (intA : SH_int_comp2 A (a,b,A_SH)) :
  SH_int_comp2 A (α,β,(A_SH.subst (a ⟹ α.tt)).subst (b ⟹ β.tt)) := by sorry

lemma helper_intro_int_inv
  (A A_SH: Formula) --(a b α β : List String)
  (intA' : SH_int_comp2 A (α,β,(A_SH.subst (a ⟹ α.tt)).subst (b ⟹ β.tt))) :
  SH_int_comp2 A (a,b,A_SH) := by sorry

lemma inf_rule_as_imp (A B C : Formula) (a : List String) (t : List Term):
  (Γ ⊢ ∀₁ x ((A∨₁(B∨₁C)).subst (HashMap.ofList (a.zip t)))) → (Γ ⊢ ∀₁ x (((A∨₁B)∨₁C).subst (HashMap.ofList (a.zip t)))) := by sorry

-- Γ ⊢ ∀₁ (a ++ (c ++ u)) ((A_SH.or (B_SH.or C_SH)).subst (HashMap.ofList ((b ++ (d ++ v)).zip (t₁⊙(a ++ (c ++ u)).tt))))

-- -------------------------------------------------------
-- INTERPRETAÇÕES DOS AXIOMAS DO CALCULO DE SHOENFIELD
-- -------------------------------------------------------

-- INTERPRETAÇÕES DO SHOENFIELD CALCULUS:

-- 1. Excluded Middle (axiom scheme): A∨(¬A)

def FormExMid (A: Formula) := (¬₁A)∨₁A
def FormExMid_matrix (A A_SH : Formula) (a b f a' : List String) := (((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))∨₁A_SH)

-- Interpretação do excluded middle (old)
lemma intExMidd
  (A A_SH: Formula) (intA: SH_int_comp2 A (a,b,A_SH))
  (f a' a₁ b₁ a₂ b₂ : List String):
  SH_int_comp2 ((¬₁A)∨₁A) (f++α,a'++β, ( (((b∃₁ a₁ a'.tt (¬₁((A_SH.subst (a⟹a₁.tt)).subst (b⟹b₁.tt)))).subst (b₁⟹f.tt⊙a₁.tt))∨₁((A_SH.subst (a⟹a₂.tt)).subst (b⟹b₂.tt))) ) ) :=
by
  have intA1 := SH_ren A A_SH intA
  cases intA1; rename_i a₁ intA1
  cases intA1; rename_i b₁ intA1
  have intA2 := SH_ren A A_SH intA
  cases intA2; rename_i a₂ intA2
  cases intA2; rename_i b₂ intA2
  have intA1not := @SH_int_comp2.neg A a₁ b₁ ((A_SH.subst (a⟹a₁.tt)).subst (b⟹b₁.tt)) f a' intA1
  have T:= SH_int_comp2.disj intA1not intA2
  sorry

-- Interpretação do excluded middle (new and good)
lemma intExMid
  (A A_SH: Formula) (intA: SH_int_comp2 A (a,b,A_SH))
  (f a' a₁ b₁ a₂ b₂ : List String):
  SH_int_comp2 ((¬₁A)∨₁A) (f++a₂,a'++b₂, ( (((b∃₁ a₁ a'.tt (¬₁((A_SH.subst (a⟹a₁.tt)).subst (b⟹b₁.tt)))).subst (b₁⟹f.tt⊙a₁.tt))∨₁((A_SH.subst (a⟹a₂.tt)).subst (b⟹b₂.tt))) ) ) :=
by
  have intA1 := @helper_intro_int a b a₁ b₁ A A_SH intA
  have intA2 := @helper_intro_int a b a₂ b₂ A A_SH intA
  have intA1not := @SH_int_comp2.neg A a₁ b₁ ((A_SH.subst (a⟹a₁.tt)).subst (b⟹b₁.tt)) f a' intA1
  exact SH_int_comp2.disj intA1not intA2

-- a tirar (probably)
lemma intExMiddd -- versão em que estava a tentar recuperar as variáveis originais com helper_intro_int_inv
  (A A_SH: Formula) (intA: SH_int_comp2 A (a,b,A_SH))
  (f a' a₁ b₁ a₂ b₂ : List String):
  SH_int_comp2 ((¬₁A)∨₁A) (f++a,a'++b, ((((b∃₁ a a'.tt (¬₁(A_SH))).subst (b⟹f.tt⊙a.tt))∨₁((A_SH))) ) ) :=
by
  have intA1 := @helper_intro_int a b a₁ b₁ A A_SH intA
  have intA2 := @helper_intro_int a b a₂ b₂ A A_SH intA
  have intA1not := @SH_int_comp2.neg A a₁ b₁ ((A_SH.subst (a⟹a₁.tt)).subst (b⟹b₁.tt)) f a' intA1
  --exact SH_int_comp2.disj intA1not intA2
  sorry

-- ----------------------------------------------------

-- 2. Substitution (axiom scheme)

lemma intSubs     -- interpretação de ∀xA(x) → A(t)
  (A B: Formula) (x : String) (f a' : List String)
  (intA: SH_int_comp2 A (a,b,A_SH)):
  SH_int_comp2 ((∀₁ [x] A)→₁B) ([x]++a++c,b++d,(((b∀₁ [x] [x'].tt ((b∀₁ a a'.tt A_SH).subst (b⟹f.tt⊙a.tt)))) →₁ ((A_SH.subst (HashMap.ofList ([(x, t)])))))) :=
by
  have intForallA := @SH_int_comp2.unbForall A a b A_SH [x] intA
  have H := @SH_imp ([x]++a) b (∀₁ [x] A)
  --exact SH_int_comp2.disj intForallA intB
  sorry
/-
lemma SH_imp     -- (A→B) = (¬A ∨ B)
  (A B : Formula)
  (intA : SH_int_comp2 A (a,b,A_SH)) (f a' : List String)
  (intB : SH_int_comp2 B (c,d,B_SH))
  (f a' : List String): SH_int_comp2 (A→₁B) (f++c, a'++d, ((((b∀₁ a a'.tt A_SH).subst (b ⟹ (f.tt⊙a.tt)))))→₁B_SH) :=
by
-/

-- ----------------------------------------------------

-- 3. Expansion (inference rule)

lemma intExpansion
  {A A_SH: Formula} (intA: SH_int_comp2 A (a,b,A_SH))
  {B B_SH: Formula} (intB: SH_int_comp2 B (c,d,B_SH)) :
  SH_int_comp2 (B∨₁A) (c++a,d++b,B_SH∨₁A_SH) :=
by
  exact SH_int_comp2.disj intB intA

-- ----------------------------------------------------

-- 4. Contraction (inference rule)

lemma intContrac
  (A : Formula) (intA: SH_int_comp2 A (a,b,A_SH))
  (α β : List String):
  SH_int_comp2 (A.or A) (a++α, b++β, ((A_SH.subst (a⟹a.tt)).subst (b⟹b.tt)).or ((A_SH.subst (a⟹α.tt)).subst (b⟹β.tt))) :=
  --SH_int_comp2 (A∨₁A) (a++α,b++β,(A_SH ∨₁ A_SH)) :=
by
  have intA1 := @helper_intro_int a b a b A A_SH intA
  have intA2 := @helper_intro_int a b α β A A_SH intA
  have intAvA := SH_int_comp2.disj intA1 intA2
  exact intAvA

-- ----------------------------------------------------

-- 5. Associativity (inference rule)

lemma intAssoc1  -- interpretação de Av(BvC)
  (A B C: Formula)
  (intA: SH_int_comp2 A (a,b,A_SH)) (intB: SH_int_comp2 B (c,d,B_SH)) (intC: SH_int_comp2 C (u,v,C_SH)):
  SH_int_comp2 (A∨₁(B∨₁C)) (a++c++u,b++d++v,(A_SH ∨₁ (B_SH ∨₁ C_SH))) :=
by
  have intOr1 := SH_int_comp2.disj intB intC
  have intOr2 := SH_int_comp2.disj intA intOr1
  rw [List.append_assoc a c u, List.append_assoc b d v]
  exact intOr2

lemma intAssoc2  -- interpretação de (AvB)vC
  (A B C: Formula)
  (intA: SH_int_comp2 A (a,b,A_SH)) (intB: SH_int_comp2 B (c,d,B_SH)) (intC: SH_int_comp2 C (u,v,C_SH)):
  SH_int_comp2 ((A∨₁B)∨₁C) (a++c++u,b++d++v,((A_SH ∨₁ B_SH) ∨₁ C_SH)) :=
by
  have intOr1 := SH_int_comp2.disj intA intB
  have intOr2 := SH_int_comp2.disj intOr1 intC
  exact intOr2

-- ----------------------------------------------------

-- 6. Cut (inference rule)

lemma intCut1  -- interpretação de AvB
  (A B: Formula)
  (intA: SH_int_comp2 A (a,b,A_SH)) (intB: SH_int_comp2 B (c,d,B_SH)):
  SH_int_comp2 (A∨₁B) (a++c,b++d,(A_SH ∨₁ B_SH)) :=
by
  exact SH_int_comp2.disj intA intB

lemma intCut2  -- interpretação de ¬AvC
  (A C: Formula)
  (intA: SH_int_comp2 A (a,b,A_SH)) (intC: SH_int_comp2 C (u,v,C_SH)):
  SH_int_comp2 ((¬₁A)∨₁C) (f++u,a'++v,(((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)) ∨₁ C_SH)) :=
by
  have intnA := @SH_int_comp2.neg A a b A_SH f a' intA
  exact SH_int_comp2.disj intnA intC

lemma intCut3  -- interpretação de B∨C
  (B C: Formula)
  (intB: SH_int_comp2 B (c,d,B_SH)) (intC: SH_int_comp2 C (u,v,C_SH)):
  SH_int_comp2 (B∨₁C) (c++u,d++v,(B_SH ∨₁ C_SH)) :=
by
  exact SH_int_comp2.disj intB intC

-- ----------------------------------------------------

-- 7. Forall introduction (inference rule)

lemma intForallInt1     -- interpretação de AvB
  (A B: Formula)
  (intA: SH_int_comp2 A (a,b,A_SH)) (intB: SH_int_comp2 B (c,d,B_SH)):
  SH_int_comp2 (A∨₁B) (a++c,b++d,(A_SH ∨₁ B_SH)) :=
by
  exact SH_int_comp2.disj intA intB

lemma intForallInt2     -- interpretação de ∀xA v B
  (A B: Formula) (x : String)
  (intA: SH_int_comp2 A (a,b,A_SH)) (intB: SH_int_comp2 B (c,d,B_SH)):
  SH_int_comp2 ((∀₁ [x] A)∨₁B) ([x]++a++c,b++d,(A_SH ∨₁ B_SH)) :=
by
  have intForallA := @SH_int_comp2.unbForall A a b A_SH [x] intA
  exact SH_int_comp2.disj intForallA intB


















-- --------------------------------------------------------------------------------------------------------
-- --------------------------------------------------------------------------------------------------------
-- --------------------------------------------------------------------------------------------------------
-- --------------------------------------------------------------------------------------------------------
-- --------------------------------------------------------------------------------------------------------
-- --------------------------------------------------------------------------------------------------------

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

-- Soundness theorem (old)
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
    . sorry
      --exact Coisa
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

-- ---------------------------------------------------
-- All formulas have an interpretation
-- ---------------------------------------------------

lemma all_formulas_have_an_interpretation {f a' : List String}:
  ∀ A, ∃ a b A_SH, SH_int_comp2 A (a, b, A_SH) :=
by
  intro A
  induction A with
  | rel R ts =>
      have hAt : isAtomic (rel R ts) := by exact isAtomic.at_rel R ts
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


-- --------------------------------------------------------------------
-- --------------------------------------------------------------------
--                         SOUNDNESS THEOREM
-- --------------------------------------------------------------------
-- --------------------------------------------------------------------

lemma Insert_bAC
  (A : Formula) (x y f a' : List String) (Γ : Set Formula)
  (h : (Γ₁ = insert (bAC x y f c d A) Γ)) : (bAC x y f c d A) ∈ Γ₁ := by sorry

theorem SoundnessTheorem
  (A B : Formula)
  --(t : List Term)
  (z : String)
  (x y f g a' c' x' y' Φ a₁ a₂ b₁ b₂: List String)
  (pa : Γ₁ ⊢ A)
  (hG : Γ₁ = insert (bAC x y f c d B) Γ)
  --(hA2 : AuSH.components = (a,b,A_SH))
  --(hA3 : isBase A_SH)
   :
  --(Provable (bAC x y f A)) →
  ∃a b A_SH,
  SH_int_comp2 A (a,b,A_SH) ∧
  ∃(t:List Term), (Γ ⊢ (∀₁ a (A_SH.subst (HashMap.ofList (b.zip (t⊙(a.tt))))))) := by
    induction pa
    /-
    . -- Ax
      rename_i AinΓ
      have h1 : A = bAC x y f c d B := by sorry
      --apply ProvableFrom.ax
      sorry
    -/
  -- ------------------------------------------------------
  --        SHOENFIELD'S CALCULUS: Axiom schema
  -- ------------------------------------------------------
    . -- Excluded Middle (exMid)
      rename_i A
      have intA := @all_formulas_have_an_interpretation f a' A
      cases intA; rename_i a intA; cases intA; rename_i b intA; cases intA; rename_i A_SH intA
      have intA1 := @helper_intro_int a b a₁ b₁ A A_SH intA
      have intA2 := @helper_intro_int a b a₂ b₂ A A_SH intA
      have intA1not := @SH_int_comp2.neg A a₁ b₁ ((A_SH.subst (a⟹a₁.tt)).subst (b⟹b₁.tt)) f a' intA1
      have intnA1vA2 := SH_int_comp2.disj intA1not intA2
      use f ++ a₂; use a' ++ b₂;
      use (((b∃₁ a₁ a'.tt (¬₁((A_SH.subst (a⟹a₁.tt)).subst (b⟹b₁.tt)))).subst (b₁⟹f.tt⊙a₁.tt)) ∨₁ ((A_SH.subst (a⟹a₂.tt)).subst (b⟹b₂.tt)))
      constructor
      . exact intnA1vA2
      . let p : List Term := λ₁ (f++a₂) ([𝔰₁]⊙(a₂.tt))
        let q : List Term := λ₁ (f++a₂) ((f.tt)⊙(a₂.tt))
        let t' : List Term := p++q
        sorry
      /-

      SH_int_comp2 ((¬₁A)∨₁A) (f++a₂,a'++b₂, ( (((b∃₁ a₁ a'.tt (¬₁((A_SH.subst (a⟹a₁.tt)).subst (b⟹b₁.tt)))).subst (b₁⟹f.tt⊙a₁.tt))∨₁((A_SH.subst (a⟹a₂.tt)).subst (b⟹b₂.tt))) ) )
      -/
      --have intA' := SH_int_comp_renaming_lemma a b x y A A_SH intA
      --have intNotA := @SH_int_comp2.neg A a b A_SH f a' intA
      --have intNotAvA' := SH_int_comp2.disj intNotA intA'
      --use f++x; use a'++y; use (((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)) ∨₁ A_SH)
      --constructor
      --. exact intNotAvA'
      --. have pq := (λ₁ (f++x) ([𝔰₁]⊙(x.tt)))++(λ₁ (f++x) ((f.tt)⊙(x.tt)))
      --  use pq
      --  --(λ₁ (f++x) ((f.tt)⊙(x.tt)))
    . -- Substitution (subs)
      rename_i x t A
      have intA := @all_formulas_have_an_interpretation f a' A
      cases intA; rename_i a intA; cases intA; rename_i b intA; cases intA; rename_i A_SH intA
      have intForallA := @SH_int_comp2.unbForall A a b A_SH [x] intA
      sorry       -- TBD: simply continue (not fully done)
  -- ------------------------------------------------------
  --        SHOENFIELD'S CALCULUS: Inference rules
  -- ------------------------------------------------------
    . -- Expansion (exp)
      rename_i A B exp1 exp2
      have intB := @all_formulas_have_an_interpretation f a' B
      cases intB; rename_i c intB; cases intB; rename_i d intB; cases intB; rename_i B_SH intB
      cases exp2; rename_i a exp2; cases exp2; rename_i b exp2; cases exp2; rename_i A_SH exp2
      cases exp2; rename_i intA soundA
      have intAvB := SH_int_comp2.disj intB intA
      use c++a; use d++b; use (B_SH ∨₁ A_SH)
      constructor
      . exact intAvB
      . cases' soundA with t₁
        let k : Term := lcons "k"
        let p : List Term := λ₁ (c++a) ([k])
        --let q : List Term := λ₁ (c++a) (t₂⊙(a.tt))
        --let t' : List Term := p++q
        sorry     -- TBD: falta a questão do combi completeness
    . -- Contraction (contrac)
      rename_i A contrac1 contrac2
      have intA := @all_formulas_have_an_interpretation f a' A
      cases intA; rename_i a intA
      cases intA; rename_i b intA
      cases intA; rename_i A_SH intA
      --have intA' := SH_int_comp_renaming_lemma a b x y A A_SH intA
      cases contrac2; rename_i K1 contrac2; cases contrac2; rename_i K2 contrac2; cases contrac2; rename_i K3 contrac2
      sorry       -- TBD: extract the tuples, not just names
    . -- Associativiy (assoc)
      rename_i A B C assoc1 assoc2
      have intA := @all_formulas_have_an_interpretation f a' A
      cases intA; rename_i a intA; cases intA; rename_i b intA; cases intA; rename_i A_SH intA
      have intB := @all_formulas_have_an_interpretation f a' B
      cases intB; rename_i c intB; cases intB; rename_i d intB; cases intB; rename_i B_SH intB
      have intC := @all_formulas_have_an_interpretation f a' C
      cases intC; rename_i u intC; cases intC; rename_i v intC; cases intC; rename_i C_SH intC
      have intBvC := SH_int_comp2.disj intB intC
      have intA_BvC := SH_int_comp2.disj intA intBvC
      have intAvB := SH_int_comp2.disj intA intB
      have intAvB_C := SH_int_comp2.disj intAvB intC
      --cases assoc2; rename_i hLeft hRight
      --
      --... not needed, já temos intA_BvC
      --let acu_l : List String := (a++c)++u
      --let acu_r : List String := a++(c++u)
      use (a++c)++u; use (b++d)++v; use (A_SH.or B_SH).or C_SH
      apply And.intro
      . exact intAvB_C
      . cases' assoc2 with aa assoc2; cases' assoc2 with bb assoc2; cases' assoc2 with AA assoc2;
        cases' assoc2 with hLeft hSound
        have H := SH_equiv_comp (A∨₁(B∨₁C)) (A_SH ∨₁ (B_SH ∨₁ C_SH)) AA (a ++ (c ++ u)) (b ++ (d ++ v)) aa bb intA_BvC hLeft
        cases' H with h_acu h_p
        cases' h_p with h_bdv h_ABC
        rw [←h_acu, ←h_bdv, ←h_ABC] at hSound
        cases' hSound with t₁ hSound2
        rw [List.append_assoc a c u, List.append_assoc b d v]
        have HH := @inf_rule_as_imp Γ ((a ++ (c ++ u))) A_SH B_SH C_SH (b ++ (d ++ v)) ((t₁⊙(a ++ (c ++ u)).tt)) hSound2
        --have H := @SH_equiv AA (A∨₁(B∨₁C)) (A_SH ∨₁ (B_SH ∨₁ C_SH)) AA (a ++ (c ++ u)) (b ++ (d ++ v)) aa bb intA_BvC hLeft
        --rw [←H] at hLeft
        use t₁
      /-
      lemma inf_rule_as_imp (A B C : Formula) (a : List String) (t : List Term):
       (Γ ⊢ ∀₁ x ((A∨₁(B∨₁C)).subst (HashMap.ofList (a.zip t)))) → (Γ ⊢ ∀₁ x (((A∨₁B)∨₁C).subst (HashMap.ofList (a.zip t)))) := by sorry

      -- Igualdades entre termos são igualdades  -- TBD: seria necessário definir substituição de termos por termos
      lemma eq_are_eq {Γ : Set Formula} (t q : Term) (h: Γ ⊢ t=₁q): t=q := by sorry

      -- Interpretações de uma mesma fórmula são equivalentes
      lemma SH_equiv (A A_SH A_'SH: Formula) (a b a' b' : List String) (h1 : SH_int_comp2 A (a,b,A_SH)) (h2 : SH_int_comp2 A (a',b',A'_SH)):
      (SH_int_comp2 A (a,b,A_SH)) ↔ (SH_int_comp2 A (a',b',A'_SH)) := by sorry
      -/

      --obtain ⟨a++(c++u), b++(d++v), (A_SH ∨₁ (B_SH ∨₁ C_SH)), cenas⟩ := assoc2
      --use a++c at assoc2
      --cases assoc2;
      --rename_i a++(c++u) assoc2;
             -- TBD: extract the tuples, not just names
    . -- Cut rule (cut)
      rename_i A B C cut1 cut2 sound1 sound2
      have intA := @all_formulas_have_an_interpretation f a' A
      cases' intA with a intA; cases' intA with b intA; cases' intA with A_SH intA
      have intB := @all_formulas_have_an_interpretation f a' B
      cases' intB with c intB; cases' intB with d intB; cases' intB with B_SH intB
      have intC := @all_formulas_have_an_interpretation f a' C
      cases' intC with u intC; cases' intC with v intC; cases' intC with C_SH intC
      have intAvB := SH_int_comp2.disj intA intB
      have intBvC := SH_int_comp2.disj intB intC
      have intNotA := @SH_int_comp2.neg A a b A_SH f a' intA
      have intNotAvC := SH_int_comp2.disj intNotA intC
      use c ++ u; use d ++ v; use (B_SH ∨₁ C_SH)
      apply And.intro
      . exact intBvC
      . -- Check: preciso de conseguir inserir specific cenas no sound1
        --let aa : List String := a++c
        --have h_specific : ∃ a, ∃ b, ∃ A_SH, (SH_int_comp2 (A.or B) (a, b, A_SH) ∧ ∃ t, Γ ⊢ ∀₁ a (A_SH.subst (HashMap.ofList (b.zip (t⊙a.tt))))) := ⟨(a++c), ⟨(b++d), ⟨(A_SH∨₁B_SH), sound1⟩⟩⟩
        --have sound3 : ∃ a b A_SH, SH_int_comp2 (A.or B) (a, b, A_SH) ∧ ∃ t, Γ ⊢ ∀₁ a (A_SH.subst (HashMap.ofList (b.zip (t⊙a.tt)))) := ⟨a++c, sound1⟩

        -- Separar hipotese sound1 nas suas componentes: retrieve soundness para AvB
        cases' sound1 with aa sound1; cases' sound1 with bb sound1; cases' sound1 with AB_SH sound1
        cases' sound1 with hLeft1 hRight1
        have H1 := SH_equiv_comp (A∨₁B) (A_SH ∨₁ B_SH) AB_SH (a++c) (b++d) aa bb intAvB hLeft1
        cases' H1 with h_ac h_p
        cases' h_p with h_bd h_AB
        rw [←h_ac, ←h_bd, ←h_AB] at hRight1
        cases' hRight1 with t₁ hCut₁          -- t₁ corresponde aos termos t,q no texto

        -- Separar hipotese sound2 nas suas componentes: retrieve soundness para ¬AvC
        cases' sound2 with cc sound2; cases' sound2 with dd sound2; cases' sound2 with AC_SH sound2
        cases' sound2 with hLeft2 hRight2
        have H2 := SH_equiv_comp ((¬₁A)∨₁C) (((b∃₁ a a'.tt A_SH.not).subst (b⟹f.tt⊙a.tt)).or C_SH) AC_SH (f++u) (a'++v) cc dd intNotAvC hLeft2
        cases' H2 with h_fu h_p
        cases' h_p with h_a'v h_AC
        rw [←h_fu, ←h_a'v, ←h_AC] at hRight2
        cases' hRight2 with t₂ hCut₂          -- t₂ corresponde aos termos r,s no texto
        sorry

      /-
      lemma SH_equiv_comp (A A_SH A_'SH: Formula) (a b a' b' : List String) (h1 : SH_int_comp2 A (a,b,A_SH)) (h2 : SH_int_comp2 A (a',b',A'_SH)):
      (a=a') ∧ (b=b') ∧ (A_SH = A'_SH) := by sorry
      -/


      --cases' sound1 with blu bla
      --sorry
             -- TBD: extract the tuples, not just names
    . -- ∀-introduction (forallInt)
      rename_i x A B h sound
      have intA := @all_formulas_have_an_interpretation f a' A
      cases intA; rename_i a intA; cases intA; rename_i b intA; cases intA; rename_i A_SH intA
      have intB := @all_formulas_have_an_interpretation f a' B
      cases intB; rename_i c intB; cases intB; rename_i d intB; cases intB; rename_i B_SH intB
      have intAvB := SH_int_comp2.disj intA intB
      have intFA := @SH_int_comp2.unbForall A a b A_SH x intA
      have intFAvB := SH_int_comp2.disj intFA intB
      use (x ++ a) ++ c; use (b++d); use (A_SH ∨₁ B_SH)
      apply And.intro
      . exact intFAvB
      . -- Separar hipotese sound nas suas componentes: retrieve soundness para AvB
        cases' sound with aa sound; cases' sound with bb sound; cases' sound with AB_SH sound
        cases' sound with hLeft hRight
        have H := SH_equiv_comp (A∨₁B) (A_SH ∨₁ B_SH) AB_SH (a++c) (b++d) aa bb intAvB hLeft
        cases' H with h_ac h_p
        cases' h_p with h_bd h_AB
        rw [←h_ac, ←h_bd, ←h_AB] at hRight
        cases' hRight with t₁ hForall
        --have termo : (t₁⊙(a ++ c).tt) = (t⊙(x ++ a ++ c).tt) := by sorry
        sorry
            -- TBD: 1. Precisamos de definir t que faça (t₁⊙(a ++ c).tt) = (t⊙(x ++ a ++ c).tt)
            --      2. then usamos o forall intro para o x and done
  -- ------------------------------------------------------
  -- Os axiomas que são universal closures of base formulas
  -- ------------------------------------------------------
    . -- repeat {} OU acrescentar lema
      rename_i z
      use [z], [], (AxiomE1_matrix z)
      have intAxE1 := AxiomE1_int z
      constructor
      . exact intAxE1
      . use []
        simp [HashMap.ofList]
        apply AxE₁
    . rename_i x₁ x₂ A hAbase
      use [x₁, x₂], [], (AxiomE2_matrix x₁ x₂ A hAbase)
      have intAxE2 := AxiomE2_int A hAbase x₁ x₂
      constructor
      . exact intAxE2
      . use []
        simp [HashMap.ofList]
        exact AxE₂
    . sorry   -- é o AxU -> falta interp de AxU
    . rename_i x₁ x₂
      use [x₁, x₂], [], (AxiomC1_matrix x₁ x₂)
      constructor
      . exact AxiomC1_int x₁ x₂
      . use []
        simp [HashMap.ofList]
        exact AxC₁
    . rename_i x₁ x₂ x₃
      use [x₁, x₂, x₃], [], (AxiomC2_matrix x₁ x₂ x₃)
      constructor
      . exact AxiomC2_int x₁ x₂ x₃
      . use []
        simp [HashMap.ofList]
        exact AxC₂
    . rename_i x₁ x₂
      use [x₁, x₂], [], (AxiomP1_matrix x₁ x₂)
      constructor
      . exact AxiomP1_int x₁ x₂
      . use []
        simp [HashMap.ofList]
        exact AxP₁
    . rename_i x₁ x₂ x₃
      use [x₁, x₂, x₃], [], (AxiomP2_matrix x₁ x₂ x₃)
      constructor
      . exact AxiomP2_int x₁ x₂ x₃
      . use []
        simp [HashMap.ofList]
        exact AxP₂
    . rename_i x₁ x₂
      use [x₁, x₂], [], (AxiomS1_matrix x₁ x₂)
      constructor
      . exact AxiomS1_int x₁ x₂
      . use []
        simp [HashMap.ofList]
        exact AxS₁
    . rename_i x₁ x₂ x₃
      use [x₁, x₂, x₃], [], (AxiomS2_matrix x₁ x₂ x₃)
      constructor
      . exact AxiomS2_int x₁ x₂ x₃
      . use []
        simp [HashMap.ofList]
        exact AxS₂
    . rename_i x₁ x₂ x₃ y
      use [x₁, x₂, x₃], [], (AxiomS3_matrix x₁ x₂ x₃ y)
      constructor
      . exact AxiomS3_int x₁ x₂ x₃ y
      . use []
        simp [HashMap.ofList]
        exact AxS₃
    . rename_i x₁ x₂
      use [x₁], [], (AxiomS4_matrix x₁ x₂)
      constructor
      . exact AxiomS4_int x₁ x₂
      . use []
        simp [HashMap.ofList]
        exact AxS₄
  -- ------------------------------------------------------
  --  O bounded axiom of choice
  -- ------------------------------------------------------
    . rename_i A' h
      --cases hG
      have H := Insert_bAC B x y f a' Γ hG
      have hAx := ProvableFrom.AxbAC H
      /-
      use [[g]++[Φ]], [[x']++[f']], [(((((b∀₁ x [var x'] (¬₁((b∀₁ [y] [var y'] (¬₁A)))))).subst ([y']⟹[var g·var x]))) →₁
      (((¬₁(b∀₁ [f] [var f'] (¬₁(b∀₁ [a] [var a'] (¬₁(b∀₁₁ b (var f·var a) (¬₁A))))))).subst
        ([a']⟹[var Φ·var f]))))]
      -/
      sorry

/- a apagar depois de provar o bAC no soundness
lemma bAC_int22
  (x y f a b : String) (A : Formula) (hAbase : isBase A) (y' g a' Φ f' : String):
  SH_int_comp2 (bAC_star_om x y f a b A) ([g]++[Φ],[x']++[f'],
    ((((b∀₁ [x] [var x'] (¬₁((b∀₁ [y] [var y'] (¬₁A)))))).subst ([y']⟹[var g·var x]))) →₁
      (((¬₁(b∀₁ [f] [var f'] (¬₁(b∀₁ [a] [var a'] (¬₁(b∀₁₁ b (var f·var a) (¬₁A))))))).subst
        ([a']⟹[var Φ·var f])))) := by sorry
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
