import LeanProjeto2.FOL
import LeanProjeto2.StarLang
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

open FOL
open LFormula

open StarLang
--open FType

-- SHOENFIELD'S FUNCTIONAL INTERPREATION

-- ---------------------------------------------------------------------------------------------------------------
--             SECTION 2.2: Shoenfield's functional interpretation
-- ---------------------------------------------------------------------------------------------------------------


-- -------------------------------------------------------------
-- DEFINITION 2.1 (p.40): Shoenfield's functional interpretation
-- -------------------------------------------------------------

/-
A^SH = ∀a ∃b A_SH (a,b) : Formula    ->    (A^ -> V a E b A_)
B^SH = ∀c ∃d B_SH (c,d) : Formula    ->    (B^ -> V c E d B_)

def SH_int : Formula → Formula
| SH_base
| SH_or
| SH_not
| SH_unb_forall
| SH_b_forall

def SH_int : Finset Term.var → Finset Term.var → Formula → Formula            -- TO DO: Precisamos do ∀₁ para tuples of variables
| SH_base
| SH_or
| SH_not
| SH_unb_forall
| SH_b_forall

def SH_int : Formula → Formula                              LISTAS DE VAR UNIV E VAR EXIST? List Term → List Term → Formula → Formula
| SH_base
    | (isBase A) => A
| V a E b A_ , V c E d B_ => V a V c E b E d (A_ ∨₁ B_)
    | {a} {b} A_ , c d B_ => {a c} {b d} (A_ ∨₁ B_)         USAR APPEND DAS LISTAS?
| SH_not
    | {a} {b} A_ =>                                         COMO CRIAR f a partir de b e a' a partir de a???
                                                            acho que precisamos de usar substitution
| SH_unb_forall
| SH_b_forall

def interp : Formula → Formula
| SH_base: (isBase A) => A




def SH_int : Formula → Formula
| Formula.lcons p ts => Formula.lcons p ts
| Formula.not A =>
  Formula.forall_L "f" (Formula.exists_L "a'" (Formula.not_L (subst_formula "a" (LTerm.Lfunc "f" [LTerm.Lvar "a"]) (SH_int A))))
| Formula.or A B =>
  let A_SH := SH_int A in
  let B_SH := SH_int B in
  Formula.forall_L "a" (Formula.exists_L "b" (subst_formula "a" (LTerm.Lvar "b") A_SH)) ∧
  Formula.forall_L "c" (Formula.exists_L "d" (subst_formula "c" (LTerm.Lvar "d") B_SH)) →
  Formula.forall_L "a" (Formula.forall_L "c" (Formula.exists_L "b" (Formula.exists_L "d" (Formula.or_L (subst_formula "a" (LTerm.Lvar "b") A_SH) (subst_formula "c" (LTerm.Lvar "d") B_SH)))))
| Formula.bForall x A =>
  let A_SH := SH_int A in
  Formula.forall_L x (Formula.forall_L "a" (Formula.exists_L "b" (subst_formula x (LTerm.Lvar "a") A_SH)))
| Formula.exists_L x A =>
  let A_SH := SH_int A in
  Formula.forall_L "a" (Formula.exists_L "b" (Formula.exists_L x (subst_formula x (LTerm.Lvar "a") A_SH)))
| Formula.bounded_forall_L x t A =>
  let A_SH := SH_int A in
  Formula.forall_L "a" (Formula.exists_L "b" (Formula.forall_L x (Formula.and_L (Formula.atomic_L "in" [LTerm.Lvar x, t]) (subst_formula x (LTerm.Lvar "a") A_SH))))

--inductive SHint : Finset String → Finset String → Formula → Formula
--| sorry

def SH_int2 : Formula → Formula
| Formula.or A B =>
  V₁ "a" (E₁ "b" (substitution_formula "a" (Term.var "b") A_SH)) →
  V₁ "c" (E₁ "d" (substitution_formula "c" (Term.var "d") B_SH)) →
  V₁ "a" (V₁ "c" (E₁ "b" (E₁ "d" ((substitution_formula "a" (Term.var "b") A_SH) ∨₁ (substitution_formula "c" (Term.var "d") B_SH)))))

-/


--inductive SH_int : Formula → Formula
--| SH_base (h: isBase A) A : SH_int

--def SH_int (α β : Finset String) (A : Formula) : Formula := ∀ α, ∃ β

-- TO DO: como falar das lower SH-formulas?

namespace StarLang.Formula

def components_neg : Formula → (Finset String × Finset String × Formula)
| .unbForall x F => let (a,b,rest) := components_neg F;
                    (a,{x} ∪ b,rest)
| F => ({},{},F)

def components : Formula → (Finset String × Finset String × Formula)
| .unbForall x F => let (a,b,rest) := components F;
                    ({x} ∪ a,b,rest)
| .not F => components_neg F
| F => ({},{},F)

end StarLang.Formula

noncomputable def recreate : (Finset String × Finset String × Formula) → Formula
| (a,b,rest) => let ex := List.foldl (fun f x => .not (.unbForall x f)) rest (b.val.toList : List String)
                List.foldl (fun f x => .unbForall x f) ex (a.val.toList : List String)

inductive SH_int : Formula → Formula → Prop                 -- TO DO: ok but how can I make computations?
| base : (h : StarLang.isBase A) → SH_int A A               -- TO DO: Doesn't capture the essence...
| disj : SH_int A AuSH →
         SH_int B BuSH →
         AuSH.components = (a,b,A_SH) →
         BuSH.components = (c,d,B_SH) →
         --({a,b} ⊆ A.allvars) →
         -- TODO: dizer lista não tem conjuntos repetidos
         --({c,d} ⊆ B.allvars) →
         --(SH_int A (V₁ a (E₁ b A_SH))) →
         --(SH_int B (V₁ c (E₁ d B_SH))) →
         (hA : StarLang.isBase A_SH) →                                      -- A^SH = ∀a ∃b A_SH(a,b)
         (hB : StarLang.isBase B_SH) →                                      -- B^SH = ∀c ∃d B_SH(c,d)
         (SH_int (A∨₁B) (recreate (a∪c,b∪d,(A_SH ∨₁ B_SH))))
         --(SH_int (A∨₁B) (V₁ a (V₁ c (E₁ b (E₁ d (A_SH ∨₁ B_SH))))))         -- (A∨B)^SH = ∀a,c ∃b,d [ A_SH(a,b) ∨ B_SH(c,d) ]
| neg {f:String}: ({a,b} ⊆ A.allvars) →
        (SH_int A (V₁ a (E₁ b A_SH))) →                                     -- A^SH = ∀a ∃b A_SH(a,b)
        (hA : StarLang.isBase A_SH) →
        ((SH_int (¬₁A) (V₁ f (E₁ a' (bE₁ a (Term.var (a')) (¬₁(substitution_formula b ((Term.var f)·(Term.var a)) A_SH)))))))   -- (¬A)^SH = ∀f ∃a' [ ∃a∈a' ¬A_SH(a,fa) ]
| unbForall : ({x,a,b} ⊆ A.allvars) →
              (SH_int A (V₁ a (E₁ b A_SH))) →                               -- A^SH = ∀a ∃b A_SH(a,b)
              (hA : StarLang.isBase A_SH) →
              (SH_int (V₁ x A) (V₁ x (V₁ a (E₁ b A_SH))))                   -- (∀x A)^SH = ∀x,a ∃b [ A_SH(x,a,b) ]
| bForall : ({x,a,b} ⊆ A.allvars) →
            -- (h : x ∉ t.freevars)
            (SH_int A (V₁ a (E₁ b A_SH))) →                                 -- A^SH = ∀a ∃b A_SH(a,b)
            (hA : StarLang.isBase A_SH) →
            (SH_int (bV₁ x t A) (V₁ a (E₁ b (bV₁ x t A_SH))))               -- (∀x∈t A(x))^SH = ∀a ∃b [ ∀x∈t A_SH(x,a,b) ]

-- função com

def Teste (a b : String) (f : Term) (A_SH : Formula): Formula := substitution_formula b (f·(Term.var a)) A_SH
-- TO DO no: mudar def de substitution para que sejam Term.var em vez de String
-- TODO: variaveis disjuntas

-- TO DO yes: falta substituição + Why V₁ f not working and diz que é term?
