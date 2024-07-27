import LeanProjeto2.FOL
import LeanProjeto2.StarLang
import MathLib.Tactic

open FOL
open LFormula

--open StarLang
--open FType

-- SHOENFIELD'S FUNCTIONAL INTERPREATION

/-
A^SH = ∀a ∃b A_SH (a,b) : Formula    ->    (A^ -> V a E b A_)
B^SH = ∀c ∃d B_SH (c,d) : Formula    ->    (B^ -> V c E d B_)

def SH_int : Formula → Formula
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



def shoenfield_interpretation : Formula → Formula
| Formula.lcons p ts => Formula.lcons p ts
| Formula.not A =>
  Formula.forall_L "f" (Formula.exists_L "a'" (Formula.not_L (subst_formula "a" (LTerm.Lfunc "f" [LTerm.Lvar "a"]) (shoenfield_interpretation A))))
| Formula.or A B =>
  let A_SH := shoenfield_interpretation A in
  let B_SH := shoenfield_interpretation B in
  Formula.forall_L "a" (Formula.exists_L "b" (subst_formula "a" (LTerm.Lvar "b") A_SH)) ∧
  Formula.forall_L "c" (Formula.exists_L "d" (subst_formula "c" (LTerm.Lvar "d") B_SH)) →
  Formula.forall_L "a" (Formula.forall_L "c" (Formula.exists_L "b" (Formula.exists_L "d" (Formula.or_L (subst_formula "a" (LTerm.Lvar "b") A_SH) (subst_formula "c" (LTerm.Lvar "d") B_SH)))))
| Formula.bForall x A =>
  let A_SH := shoenfield_interpretation A in
  Formula.forall_L x (Formula.forall_L "a" (Formula.exists_L "b" (subst_formula x (LTerm.Lvar "a") A_SH)))
| Formula.exists_L x A =>
  let A_SH := shoenfield_interpretation A in
  Formula.forall_L "a" (Formula.exists_L "b" (Formula.exists_L x (subst_formula x (LTerm.Lvar "a") A_SH)))
| Formula.bounded_forall_L x t A =>
  let A_SH := shoenfield_interpretation A in
  Formula.forall_L "a" (Formula.exists_L "b" (Formula.forall_L x (Formula.and_L (Formula.atomic_L "in" [LTerm.Lvar x, t]) (subst_formula x (LTerm.Lvar "a") A_SH))))

--inductive SHint : Finset String → Finset String → Formula → Formula
--| sorry


-/

--inductive shoenfield_interpretation : Formula → Formula
--| SH_base (h: isBase A) A : shoenfield_interpretation

--def SH_int (α β : Finset String) (A : Formula) : Formula := ∀ α, ∃ β
