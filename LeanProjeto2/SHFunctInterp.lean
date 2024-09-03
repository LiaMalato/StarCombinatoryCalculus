-- -------------------------------------------------------------
--          SHOENFIELD'S FUNCTIONAL INTERPRETATION
-- -------------------------------------------------------------

import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.Axioms
import LeanProjeto2.StarLanguage.ResultsAndOtherDefinitions
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic


open FOLang
open LFormula
open Term
open Formula
open Batteries

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
-/

-- É PRECISO ACRESCENTAR ISFULLYBASE, aka que temos necessariamente uma fórmula sem ∀ e sem ∃ na matriz

#check isBase

def Formula.components : Formula → (Finset String × Finset String × Formula)
| unbForall x A =>
    let (a, b, rest) := A.components
    ({x} ∪ a, b, rest)
| not (unbForall x A) =>
    let (a, b, rest) := A.components
    (a, {x} ∪ b, rest)
| not A =>
    let (a, b, rest) := A.components
    (a, b, not rest)
--| bForall x t A =>
--    let (a, b, rest) := A.components
--    (a, {x} ∪ b, bForall x t rest)
| or A1 A2 =>
    let (a1, b1, r1) := A1.components
    let (a2, b2, r2) := A2.components
    (a1 ∪ a2, b1 ∪ b2, or r1 r2)
| A => ({}, {}, A)
-- Reunião: daria se calhar para pôr aqui um not e forall
-- Só se pode usar quando ja estiver com ∀a ∃b

def Formula.components2 : Formula → (List String × List String × Formula)
| unbForall x A =>
    let (a, b, rest) := A.components2
    ({x} ∪ a, b, rest)
| not (unbForall x A) =>
    let (a, b, rest) := A.components2
    (a, {x} ∪ b, rest)
| not A =>
    let (a, b, rest) := A.components2
    (a, b, not rest)
--| bForall x t A =>
--    let (a, b, rest) := A.components
--    (a, {x} ∪ b, bForall x t rest)
| or A1 A2 =>
    let (a1, b1, r1) := A1.components2
    let (a2, b2, r2) := A2.components2
    (a1 ∪ a2, b1 ∪ b2, or r1 r2)
| A => ({}, {}, A)


def Formula.components5 : Formula → (List String × List String × Formula)
| unbForall x A =>
    let (a, b, rest) := A.components5
    ({x} ∪ a, b, rest)
| not (unbForall x A) =>
    let (a, b, rest) := A.components5
    (b, {x} ∪ a, not rest)
| not (not A) =>
    -- This handles the double negation case
    A.components5
| not A =>
    let (a, b, rest) := A.components5
    (b, a, not rest)
| or A1 A2 =>
    let (a1, b1, r1) := A1.components5
    let (a2, b2, r2) := A2.components5
    (a1 ∪ a2, b1 ∪ b2, or r1 r2)
| bForall x t A =>
    let (a, b, rest) := A.components5
    (a, {x} ∪ b, bForall x t rest)
| A => ([], [], A)

def Formula.dia : Formula → List String → List String → Formula → Prop
| F, u, e, f => F.components5 = (u, e, f)


example (A:Formula) : A.dia u e f1 → u == ["x"] := by sorry



-- -------
-- Example to use components:
-- -------

def formula_teste (A:Formula) : Formula := (∀₁₁ "x" (∃₁₁ "y" (∃₁₁ "z" (¬₁A))))
#eval (formula_teste (Formula.rel "R" [var_x,var_y])).components      -- Output: ({x}, {y, z}, ¬₁R(x,y)) --> CAN I ADD SIMP??
#eval components (∀₁₁ "x" (¬₁(∀₁₁ "y" (rel "P" [var_x, var_y]))))     -- Output: ({x}, {y, z}, ¬₁R(x,y))
#eval components (∀₁₁ "x" ((∃₁₁ "y" (¬₁(rel "P" [var_x, var_y])))))   -- Output: ({x}, {y, z}, ¬₁R(x,y))

def exampleFormula : Formula :=
  b∀₁₁ "x" (Term.var "t") (¬₁ (∀₁₁ "y" (Formula.rel "R" [])))
#eval exampleFormula.components       -- Output dá ({}, {x,y}, ∀x∈t R[]) --> WRONG


noncomputable def Recreate : (Finset String × Finset String × Formula) → Formula
| (a, b, rest) => -- Assim já ficamos com (x,y,F)
  -- Negações dentro do b
                let neg := List.foldl (fun f x => .unbForall x (.not f)) rest (b.val.toList : List String)
  -- unbForall dentro do a
                List.foldl (fun f x => .unbForall x f) neg (a.val.toList : List String)
-- TBD (Reunião): dá para acrescentar aqui que rest is always base?
--   -> Não vai ser consequência direta de acrescentar isBase como hipotese em components?

def Recreate2 : (List String × List String × Formula) → Formula
| (a, b, rest) =>
  -- Negações dentro do b
  let neg := List.foldl (fun f x => .unbForall x (.not f)) rest b
  -- unbForall dentro do a
  List.foldl (fun f x => Formula.unbForall x f) neg a

def Recreate22 : (List String × List String × Formula) → Formula
| (a, b, rest) =>
  -- Negações dentro do b
  let neg := List.foldl (fun f x => .unbForall x (.not f)) rest b
  -- unbForall dentro do a
  List.foldl (fun f x => Formula.unbForall x f) neg a

def Recreate3 : (List String × List String × Formula) → Formula
| (a, b, rest) =>
  -- Apply universal quantifiers first
  let apply_unbForall := List.foldl (fun f x => Formula.unbForall x f) rest a
  -- Apply negations to existential quantifiers
  let apply_negations := List.foldl (fun f x => Formula.not (Formula.unbForall x (Formula.not f))) apply_unbForall b
  apply_negations

def Recreate4 : (List String × List String × Formula) → Formula
| (a, b, rest) =>
  -- Apply universal quantifiers from `a` first
  let with_unbForalls := List.foldr (fun x f => Formula.unbForall x f) rest a
  -- Apply negations to existential quantifiers from `b` and wrap in the universal quantifiers
  let apply_negations := List.foldl (fun f x => Formula.not (Formula.unbForall x (Formula.not f))) with_unbForalls b
  apply_negations

def Recreate5 : (List String × List String × Formula) → Formula
| (a, b, rest) =>
  -- Apply universal quantifiers from `a` in the order they appear
  let with_unbForalls := List.foldr (fun x f => Formula.unbForall x f) rest a
  -- Apply existential quantifiers from `b` in reverse order with negations
  List.foldl (fun f x => Formula.not (Formula.unbForall x (Formula.not f))) with_unbForalls b

def Recreate6 : (List String × List String × Formula) → Formula
| (a, b, rest) =>
  -- Apply universal quantifiers from `a` in the order they appear
  let with_unbForalls := List.foldr (fun x f => Formula.unbForall x f) rest a
  -- Apply existential quantifiers from `b` in reverse order with negations
  List.foldr (fun x f => (Formula.unbForall x f)) with_unbForalls b

def Recreate7 : (List String × List String × Formula) → Formula
| (a, b, rest) =>
  -- Apply universal quantifiers from `a` in the order they appear
  let with_existentials := List.foldr (fun x f => .not (Formula.unbForall x (.not f))) rest b
  -- Apply existential quantifiers from `b` in reverse order with negations
  List.foldr (fun x f => (Formula.unbForall x f)) with_existentials a



-- --------------------------------------
-- DEFINITION 2.1 (p.38):
-- Shoenfield's functional interpretation
-- --------------------------------------

/-
Here we will represent an interpretation A^SH such as ∀a∃b A_SH(a,b) as
                  ( SH_int A^SH ( Recreate (a,b,A_SH) ) )
              ( SH_int upperSH ( Recreate (univ_var,exist_var,lowerSH) ) )
-/


-- TBD (Reunião): variaveis disjuntas -> Finset já tem disjunto
--                make List α to Finset -> List.toFinset _
-- a∪b∪c∪d : Finset     -> ver Disjoint a b c d
inductive SH_int : Formula → Formula → Prop
| base : (h : isFullyBase A) → (SH_int A (Recreate ({},{},A)))
| disj : SH_int A AuSH →
         SH_int B BuSH →
         AuSH.components = (a,b,A_SH) →                                     -- A^SH = ∀a ∃b A_SH(a,b)
         BuSH.components = (c,d,B_SH) →                                     -- B^SH = ∀c ∃d B_SH(c,d)
         --({a,b} ⊆ A.allvars) →                                            -- TO DO: precisamos?
         --({c,d} ⊆ B.allvars) →                                            -- TO DO: dizer lista não tem conjuntos repetidos
         (hA : isFullyBase A_SH) →
         (hB : isFullyBase B_SH) →
         (SH_int (A∨₁B) (Recreate (a∪c,b∪d,(A_SH ∨₁ B_SH))))                -- (A∨B)^SH = ∀a,c ∃b,d [ A_SH(a,b) ∨ B_SH(c,d) ]
| neg {f a':String}:
        -- ({a,b} ⊆ A.allvars) →
        SH_int A AuSH →
        AuSH.components = (a,b,A_SH) →                                     -- A^SH = ∀a ∃b A_SH(a,b)
        (hA : isFullyBase A_SH) →
        (SH_int (¬₁A) (Recreate (b,b,A_SH)))--(TermTupleApp (makeTuple [Term.var f]) a)))) --→  -- TODO: apagar porque foi batota
        --(SH_int (¬₁A) (Recreate ({f},{a'},(b∃₁ a.toList (Term.var a') (¬₁(substitution_formula b.toList ((Term.var f)·(Term.var a)) A_SH))))))
        --(SH_int (¬₁A) (Recreate ({f},{a'},(b∃₁ a.toList (Term.var a') A))))
        --(SH_int (¬₁A) (Recreate ({f},{a'},(b∃₁ a.toList (Term.var a') (¬₁(substitution_formula b.toList ((Term.var f)·(Term.var a)) A_SH))))))      -- TO DO / Problema: problema: o bE₁ devia então aceitar Finset String :'(
        --((SH_int (¬₁A) (V₁ f (E₁ a' (bE₁ a (Term.var (a')) (¬₁(substitution_formula b ((Term.var f)·(Term.var a)) A_SH)))))))         -- (¬A)^SH = ∀f ∃a' [ ∃a∈a' ¬A_SH(a,fa) ]
        --(SH_int2 (¬₁A) (Recreate2 (b,b,(bForallTuple2 a (ls_lt a') A_SH))))--(TermTupleApp (makeTuple [Term.var f]) a)))) --→  -- TODO: apagar porque foi batota
        --(SH_int2 (¬₁A) (Recreate2 (f,a',(b∃₁ a (Term.var a') A_SH))))

| unbForall : SH_int A AuSH →
              AuSH.components = (a,b,A_SH) →                                -- A^SH = ∀a ∃b A_SH(a,b)
              --({x,a,b} ⊆ A.allvars) →
              --(SH_int A (V₁ a (E₁ b A_SH))) →                             -- A^SH = ∀a ∃b A_SH(a,b)
              (hA : isFullyBase A_SH) →
              (SH_int (∀₁₁ x A) (Recreate (a∪{x},b,A_SH)))                  -- (∀x A)^SH = ∀x,a ∃b [ A_SH(x,a,b) ]
| bForall : SH_int A AuSH →
            AuSH.components = (a,b,A_SH) →                                  -- A^SH = ∀a ∃b A_SH(a,b)
            (hA : isFullyBase A_SH) →
            (SH_int (b∀₁ x t A) (Recreate (a,b,(b∀₁ x t A_SH))))            -- (∀x∈t A(x))^SH = ∀a ∃b [ ∀x∈t A_SH(x,a,b) ]
            --({x,a,b} ⊆ A.allvars) →
            --(h : x ∉ t.freevars)

-- TO DO (eu): a tirar este Teste e fazer um melhor
def Teste (a b : String) (f : Term) (A_SH : Formula): Formula := substitution_formula b (f·(Term.var a)) A_SH

example (A:Formula) (H : isBase A) : isBase (b∃₁₁ x t A) := by
  exact bExists_base x t H


inductive SH_int2 : Formula → Formula → Prop
| base : (h : isFullyBase A) → (SH_int2 A (Recreate ({},{},A)))
| disj : SH_int2 A AuSH →
         SH_int2 B BuSH →
         AuSH.components2 = (a,b,A_SH) →                                     -- A^SH = ∀a ∃b A_SH(a,b)
         BuSH.components2 = (c,d,B_SH) →                                     -- B^SH = ∀c ∃d B_SH(c,d)
         --({a,b} ⊆ A.allvars) →                                            -- TO DO: precisamos?
         --({c,d} ⊆ B.allvars) →                                            -- TO DO: dizer lista não tem conjuntos repetidos
         (hA : isFullyBase A_SH) →
         (hB : isFullyBase B_SH) →
         (SH_int2 (A∨₁B) (Recreate2 (a∪c,b∪d,(A_SH ∨₁ B_SH))))                -- (A∨B)^SH = ∀a,c ∃b,d [ A_SH(a,b) ∨ B_SH(c,d) ]
| neg {f a': List String}:
        -- ({a,b} ⊆ A.allvars) →
        SH_int2 A AuSH →
        (a,b,A_SH) = AuSH.components2 →                                    -- A^SH = ∀a ∃b A_SH(a,b)
        (hA : isFullyBase A_SH) →
        (SH_int2 (¬₁A) (Recreate2 (f,a',(bForallTuple2 a (ls_lt a') (¬₁(A_SH.subst (HashMap.ofList  (b.zip ((f.tt)⊙(a.tt))))))))))
| unbForall : SH_int2 A AuSH →
              AuSH.components2 = (a,b,A_SH) →                                -- A^SH = ∀a ∃b A_SH(a,b)
              --({x,a,b} ⊆ A.allvars) →
              --(SH_int A (V₁ a (E₁ b A_SH))) →                             -- A^SH = ∀a ∃b A_SH(a,b)
              (hA : isFullyBase A_SH) →
              (SH_int2 (∀₁₁ x A) (Recreate2 (a∪{x},b,A_SH)))                  -- (∀x A)^SH = ∀x,a ∃b [ A_SH(x,a,b) ]
| bForall : SH_int2 A AuSH →
            AuSH.components2 = (a,b,A_SH) →                                  -- A^SH = ∀a ∃b A_SH(a,b)
            (hA : isFullyBase A_SH) →
            (SH_int2 (b∀₁ x t A) (Recreate2 (a,b,(b∀₁ x t A_SH))))            -- (∀x∈t A(x))^SH = ∀a ∃b [ ∀x∈t A_SH(x,a,b) ]
            --({x,a,b} ⊆ A.allvars) →
            --(h : x ∉ t.freevars)

example (A B:Formula) (H : SH_int2 (A→₁B) IMPuSH) {f a' :List String}:
  (isFullyBase A_SH) → (SH_int2 A AuSH) → ((a,b,A_SH) = AuSH.components2) →
  (isFullyBase B_SH) → (SH_int2 B BuSH) → ((c,d,B_SH) = AuSH.components2) →
  ((IMPuSH.components2 = (f∪c,a'∪d,(A_SH →₁ B_SH)))) := by sorry

/-
example (A B:Formula) (H : SH_int2 (A→₁B) IMPuSH) {f a' :List String}:
  (isFullyBase A_SH) → (SH_int2 A AuSH) → ((a,b,A_SH) = AuSH.components2) →
  (isFullyBase B_SH) → (SH_int2 B BuSH) → ((c,d,B_SH) = AuSH.components2) →
  ((IMPuSH.components2 = (f∪c,a'∪d,(A_SH →₁ B_SH)))) :=
  by
    intro baseA
    intro interpA
    intro compA
    intro baseB
    intro interpB
    intro compB
    unfold F_implies
    have HH := @SH_int2.neg A AuSH a b A_SH f a' interpA compA
    sorry

-- Vamos mostrar que se A^SH = ∀a ∃b A_SH e B^SH = ∀c B_SH que (A∨B)^SH = ∀a,c ∃b (A_SH ∨ B_SH)



example (A B:Formula) (H : SH_int2 (A→₁B) IMPuSH) {f a' :List String}:
  (isFullyBase A_SH) → (SH_int2 A AuSH) → ((a,b,A_SH) = AuSH.components2) →
  (isFullyBase B_SH) → (SH_int2 B BuSH) → ((c,d,B_SH) = AuSH.components2) →
  ((IMPuSH.components2 = (f∪c,a'∪d,(A_SH →₁ B_SH)))) :=
-/
def exAA (a b : List String) (A_SH : Formula) : Formula := ∀₁ a (∃₁ b A_SH)
def exBB (c : List String) (B_SH : Formula) : Formula := ∀₁ c B_SH
def aaa : Term := var "a"
def bbb : Term := var "b"
def xx : List String := ["x"]
def yy : List String := ["y"]
def zz : List String := ["z"]
def FormulaF : Formula := aaa =₁ bbb

#check exAA xx yy FormulaF                 -- Formula ∀ "x"
#check (exAA xx yy FormulaF).components2
#eval (exAA xx yy FormulaF).components2

#eval (∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y")))              -- Formula ∀ "x" ∃ "y" (x=y)
#eval (∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components2  -- no
#eval (∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components5  -- yes

def ThisTeste := (∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components2
#eval Recreate2 ((∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components2)
#eval Recreate2 ((∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components5)
#eval Recreate5 ((∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components5)
#eval Recreate7 ((∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components5)  -- yes


--theorem Soundness (A : Formula) (hA1 : SH_int2 A AuSH) (hA2 : AuSH.components2 = (a,b,A_SH)) (hA3 : isBase A_SH):
-- (insert (bAC x y f B) ∅ ⊢ A) → (∃(t: List Term), (Provable (∀₁ a (A_SH.subst (HashMap.ofList (b.zip ((f.tt)⊙(a.tt)))))))) := by sorry    -- TBD: falta subst aqui


/- Next tarefas:
    1. Pôr namespaces para os exemplos:
        a) No FOLanguage
        b) Axioms / FiniteTypes / Syntax / ResultsAndOtherDefinitions
    2. Resolver isBase como hipotese em components... done?
    3. Resolver Term.application para tuples -> Notation 1.4

axiom Bla (A:Formula) : (¬₁(¬₁ A))=A
-/