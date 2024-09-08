-- -------------------------------------------------------------
--          SHOENFIELD'S FUNCTIONAL INTERPRETATION
-- -------------------------------------------------------------

import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.Axioms2
import LeanProjeto2.StarLanguage.ResultsAndOtherDefinitions
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Sigma
import Mathlib.Data.List.Basic


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


-- OBS: Components é para termos as components de um interpretação!
-- Só se pode usar quando ja estiver com ∀a ∃b ...
def Formula.components : Formula → (List String × List String × Formula)
| unbForall x A =>
    let (a, b, rest) := A.components
    ([x]++a, b, rest)
| not (unbForall x A) =>
    let (a, b, rest) := A.components
    (b, [x]++a, not rest)
| not (not A) =>
    -- This handles the double negation case
    A.components
| not A =>
    let (a, b, rest) := A.components
    (b, a, not rest)
| or A1 A2 =>
    let (a1, b1, r1) := A1.components
    let (a2, b2, r2) := A2.components
    (a1 ++ a2, b1 ++ b2, or r1 r2)
| bForall x t A =>
    let (a, b, rest) := A.components
    (a, b, bForall x t rest)
    --(a, [x] ∪ b, bForall x t rest)
| A => ([], [], A)


-- -------
-- Example to use components:
-- -------

def ex_formula_comp1 (A:Formula) : Formula := (∀₁₁ "x" (∃₁₁ "y" (∃₁₁ "z" (¬₁A))))
#eval (ex_formula_comp1 (Formula.rel "R" [var_x,var_y])).components               -- Output: ([x], [y, z], ¬₁R(x,y))
#eval components (∀₁₁ "x" (¬₁(∀₁₁ "y" (rel "P" [var_x, var_y]))))                 -- Output: ([x], [y, z], ¬₁R(x,y))
#eval components (∀₁₁ "x" ((∃₁₁ "y" (¬₁(rel "P" [var_x, var_y])))))               -- Output: ([x], [y, z], ¬₁R(x,y))

def ex_formula_comp2 : Formula :=
  ∀₁ ["x"] (¬₁ (b∀₁₁ "y" (Term.var "t") (Formula.rel "R" [var "y"])))
#eval ex_formula_comp2.components                                                 -- Output: (["x"], [], ∀y∈t R[y])

-- --------
-- Recreate
-- --------

@[simp]
def RecreateSimp : (List String × List String × Formula) → Formula
| (a, b, rest) => ∀₁ a (∃₁ b rest)

@[simp]
def Recreate : (List String × List String × Formula) → Formula
| ([], [], rest) => rest
| (a, [], rest) => ∀₁ a rest
| ([], b, rest) => ∃₁ b rest
| (a, b, rest) => ∀₁ a (∃₁ b rest)

-- --------------------------------------
-- DEFINITION 2.1 (p.38):
-- Shoenfield's functional interpretation
-- --------------------------------------

/-
Here we will represent an interpretation A^SH such as ∀a∃b A_SH(a,b) as
                  ( SH_int A^SH ( Recreate (a,b,A_SH) ) )
              ( SH_int upperSH ( Recreate (univ_var,exist_var,lowerSH) ) )
-/

-- TO DO (eu): a tirar este Teste e fazer um melhor
def Teste (a b : String) (f : Term) (A_SH : Formula): Formula := substitution_formula b (f·(Term.var a)) A_SH

inductive SH_int2 : Formula → Formula → Prop
| base : (h : isBase A) → (SH_int2 A A)
| disj : SH_int2 A AuSH →
         SH_int2 B BuSH →
         AuSH.components = (a,b,A_SH) →                                     -- A^SH = ∀a ∃b A_SH(a,b)
         BuSH.components = (c,d,B_SH) →                                     -- B^SH = ∀c ∃d B_SH(c,d)
         (SH_int2 (A∨₁B) (Recreate (a++c,b++d,(A_SH ∨₁ B_SH))))           -- (A∨B)^SH = ∀a,c ∃b,d [ A_SH(a,b) ∨ B_SH(c,d) ]
| neg {f a': List String}:
        SH_int2 A AuSH →
        (a,b,A_SH) = AuSH.components →                                      -- A^SH = ∀a ∃b A_SH(a,b)
        (SH_int2 (¬₁A) (Recreate (f,a',(b∃₁ a (a'.tt) (¬₁(A_SH.subst (HashMap.ofList  (b.zip ((f.tt)⊙(a.tt))))))))))
| unbForall : SH_int2 A AuSH →
              AuSH.components = (a,b,A_SH) →                                -- A^SH = ∀a ∃b A_SH(a,b)
              (SH_int2 (∀₁₁ x A) (Recreate (a++[x],b,A_SH)))             -- (∀x A)^SH = ∀x,a ∃b [ A_SH(x,a,b) ]
| bForall : SH_int2 A AuSH →
            AuSH.components = (a,b,A_SH) →                                  -- A^SH = ∀a ∃b A_SH(a,b)
            (SH_int2 (b∀₁ x t A) (Recreate (a,b,(b∀₁ x t A_SH))))       -- (∀x∈t A(x))^SH = ∀a ∃b [ ∀x∈t A_SH(x,a,b) ]

--(hA : isBase A_SH) →
-- ({a,b} ⊆ A.allvars) →
--({x,a,b} ⊆ A.allvars) →
--(h : x ∉ t.freevars)


-- Notação para HashMap.ofList (x.zip t)
def with_t (x : List String) (t : List Term) := HashMap.ofList (x.zip t)

notation x "⟹" t => with_t x t


example (h1: SH_int2 A AuSH) (h2 : AuSH.components = (a,b,A_SH))
        (h3: SH_int2 (∀₁₁ x A) interp) : interp.components = ([x]++a,b,A_SH) := by
  let H := @SH_int2.unbForall A AuSH a b A_SH x h1 h2
  sorry

inductive SH_int_comp : Formula → (List String × List String × Formula) → Prop
| base : (h : isBase A) → (SH_int_comp A ([],[],A))
| disj : SH_int_comp A (a,b,A_SH) →
         SH_int_comp B (c,d,B_SH) →
         (SH_int_comp (A∨₁B) (a++c,b++d,(A_SH ∨₁ B_SH)))               -- (A∨B)^SH = ∀a,c ∃b,d [ A_SH(a,b) ∨ B_SH(c,d) ]
| neg {f a': List String}:
        SH_int_comp A (a,b,A_SH) →
        (SH_int_comp (¬₁A) (f,a',(b∃₁ a (a'.tt) (¬₁(A_SH.subst ((b ⟹ ((f.tt)⊙(a.tt)))))))))
-- (SH_int_comp (¬₁A) (f,a',(b∃₁ a (a'.tt) (¬₁(A_SH))     ).subst (HashMap.ofList (b.zip ((f.tt)⊙(a.tt)))          ))
| unbForall : SH_int_comp A (a,b,A_SH) →
              (SH_int_comp (∀₁₁ x A) ([x]++a,b,A_SH))                 -- (∀x A)^SH = ∀x,a ∃b [ A_SH(x,a,b) ]
| bForall : SH_int_comp A (a,b,A_SH) →
            (SH_int_comp (b∀₁ x t A) (a,b,(b∀₁ x t A_SH)))            -- (∀x∈t A(x))^SH = ∀a ∃b [ ∀x∈t A_SH(x,a,b) ]

inductive SH_int_comp2 : Formula → (List String × List String × Formula) → Prop
| base : (h : isBase A) → (SH_int_comp2 A ([],[],A))
| disj : SH_int_comp2 A (a,b,A_SH) →
         SH_int_comp2 B (c,d,B_SH) →
         (SH_int_comp2 (A∨₁B) (a++c,b++d,(A_SH ∨₁ B_SH)))               -- (A∨B)^SH = ∀a,c ∃b,d [ A_SH(a,b) ∨ B_SH(c,d) ]
| neg {f a': List String}:
        SH_int_comp2 A (a,b,A_SH) →
        (SH_int_comp2 (¬₁A) (f,a',   (  (b∃₁ a (a'.tt) (¬₁(A_SH))).subst ((b ⟹ ((f.tt)⊙(a.tt))))  )     ))
-- (SH_int_Comp (¬₁A) (f,a',(b∃₁ a (a'.tt) (¬₁(A_SH))     ).subst (HashMap.ofList (b.zip ((f.tt)⊙(a.tt)))          ))
| unbForall : SH_int_comp2 A (a,b,A_SH) →
              (SH_int_comp2 (∀₁ x A) (x++a,b,A_SH))                 -- (∀x A)^SH = ∀x,a ∃b [ A_SH(x,a,b) ]
| bForall : SH_int_comp2 A (a,b,A_SH) →
            (SH_int_comp2 (b∀₁ x t A) (a,b,(b∀₁ x t A_SH)))            -- (∀x∈t A(x))^SH = ∀a ∃b [ ∀x∈t A_SH(x,a,b) ]

def coisa (x y : String) := (var x =₁ var y)
#check ¬₁ (coisa "x" "y")





--({a,b} ⊆ A.allvars) →
--({c,d} ⊆ B.allvars) →
--({x,a,b} ⊆ A.allvars) →
--(h : x ∉ t.freevars)

-- variaveis disjuntas -> Finset já tem disjunto
-- a∪b∪c∪d : Finset     -> ver Disjoint a b c d

-- ------------------------------------------------------

-- DEFINITION: Interpretation of base formulas is the base formulas themselves

@[simp]
def baseBase (A:Formula) (hA : isBase A) (hIntA: SH_int2 A AuSH) (hAcomp: AuSH.components = ({},{},A_SH))
  := A_SH = A

@[simp] -- DEFINITION: If A is base, then the lower SH-formula is equal to A
def baseBase_comp (A:Formula) (hA : isBase A) (hIntA: SH_int_comp2 A ([],[],A_SH))
  := A_SH = A

@[simp] -- DEFINITION: If A is base, then the interpretation of A is equal to A
def baseBase_rec (A:Formula) (hA : isBase A) (hIntA: SH_int_comp2 A ([],[],A_SH))
  := (Recreate ([],[],A_SH)) = A

-- ------------------------------------------------------

inductive SH_int_type : Type
| mk : List String → List String → Formula → SH_int_type

def SH_int_Comp : SH_int_type → (List String × List String × Formula)
| SH_int_type.mk a b A_SH => (a, b, A_SH)

def extract_tuple {A : Formula} {a b a' f : List String} {A_SH : Formula}
  (hA : SH_int_comp2 A (a, b, A_SH)) (hB : SH_int_comp2 B (c, d, B_SH)) : (List String × List String × Formula) :=
  match A with
  | (.or A B)           => (a++c, b++d, A)
  | (.not A)            => (f,a',((b∃₁ a (a'.tt) (¬₁(A_SH))).subst (b ⟹ ((f.tt)⊙(a.tt)))))
  | (.unbForall x A)    => (a++[x],b,A_SH)
  | (.bForall x t A)    => (a,b,(b∀₁₁ x t A_SH))
  | A                   => ([],[],A)

def extract_tuple_base {A: Formula} (hA : isBase A)
  (hAint : SH_int_comp2 A ([], [], A)) : (List String × List String × Formula) :=
  ([], [], A)

/-
def extract_tuple_base {A A_SH: Formula} (hA : isBase A)
  (hAint : SH_int_comp A ([], [], A)) : (List String × List String × Formula) :=
  ([], [], A)
-/

-- --------------------------------------------------------------
-- EXAMPLE 2.1 (p.38)
-- Interpretation of (A ∨ (∀x∈t B(x))), with B(x) a base formula.
-- --------------------------------------------------------------

--#check List.union_nil

lemma List.cons_eq (head:A) (tl1 tl2: List A) : tl1 = tl2 → h :: tl1 = h :: tl2 := by sorry

@[simp]
lemma List.union_nilTPC (l : List String) (heq : eraseDup l = l) : l ∪ [] = l := by sorry

@[simp]
lemma List.union_nil (l : List String): l ∪ [] = l := by sorry

-- Example teste: (∀₁₁ x A)^SH = ∀ a,x ∃ b A_SH
example (h: SH_int_comp2 A (a,b,A_SH)) :
        SH_int_comp2 (∀₁ x A) (x++a,b,A_SH) :=
by
  exact @SH_int_comp2.unbForall A a b A_SH x h

-- EXAMPLE 2.1: (A ∨ (∀x∈t B(x)))^SH = ∀a ∃b (A_SH ∨₁ (b∀₁ [x] t B))
example (A B : Formula) (hA: SH_int_comp2 A (a,b,A_SH)) (hB : isBase B) :
        SH_int_comp2 (A ∨₁ (b∀₁ [x] t B)) (a,b,(A_SH ∨₁ (b∀₁ [x] t B))) :=
by
  have intB := SH_int_comp2.base hB                                                             -- B
  have intForall := @SH_int_comp2.bForall B [] [] B [x] t intB                                  -- ∀x∈t B(x)
  have intOr := @SH_int_comp2.disj A a b A_SH (b∀₁ [x] t B) [] [] (b∀₁ [x] t B) hA intForall    -- A_SH ∨ ∀x∈t B(x)
  have Ha := a.append_nil
  have Hb := b.append_nil
  rw [Ha,Hb] at intOr
  exact intOr

-- ---------------------------------------------------------------------
-- EXAMPLE 2.2 (p.38)
-- Interpretation of ∀y∈t ¬(∃x ¬A(x) ∧ B(y)).
-- ---------------------------------------------------------------------

lemma ex_2_2_PrimSymbb (A B : Formula) (x y : List String) (t : List Term) : (b∀₁ y t (¬₁((∃₁ x (¬₁A))∧₁B))) = (b∀₁ y t ((∀₁ x A)∨₁(¬₁B))) :=
by
  rw [DeMorgan_and (∃₁ x (¬₁A)) B]
  unfold unbExistsTuple
  rw [DoubleNeg, DoubleNeg]

-- VERSAO ERRADA
-- EXAMPLE 2.2: (∀y∈t ¬(∃x ¬A(x) ∧ B(y)))^SH = ∀a ∃b (A_SH ∨₁ (b∀₁ [x] t B))
example (A B : Formula)
        (intA: SH_int_comp A (a,b,A_SH))
        (intB: SH_int_comp B (c,d,B_SH)) :
        SH_int_comp (b∀₁ y t (¬₁((∃₁ x (¬₁ A))∧₁B))) (x++a++g,b++c',(b∀₁ y t (A_SH ∨₁ (b∃₁ c (c'.tt) (¬₁(B_SH.subst (HashMap.ofList (d.zip ((g.tt)⊙(c.tt)))))))))) :=
by
  sorry
  --rw [ex_2_2_PrimSymbb A B x y t]                                       -- ∀y∈t ¬ (∀x A(x) ∨ ¬B(y))
  --have intForallA := @SH_int_comp.unbForall A a b A_SH x intA             -- ∀x,a ∃b A_SH(x,a,b)
  --have intNotB := @SH_int_comp.neg B c d B_SH g c' intB                   -- ∀g ∃c' [∃ c c' ¬B_SH(c,gc)]
  --have intOr := SH_int_comp.disj intForallA intNotB                     -- ∀x,a,g ∃b,c' [A_SH(x,a,b) ∨ (∃ c c' ¬B_SH(c,gc))]
  --let Form_SH := (A_SH ∨₁ (b∃₁ c (c'.tt) (¬₁(B_SH.subst (d ⟹ (g.tt⊙c.tt))))))
  --exact @SH_int_comp.bForall ((∀₁₁ x A).or B.not) ([x]++ a++g) (b ++ c') Form_SH [y] [t] intOr        -- ∀x,a,g ∃b,c' [∀y∈t (A_SH(x,a,b) ∨ (∃ c c' ¬B_SH(c,gc)))]

-- VERSAO CERTA
-- EXAMPLE 2.2: (∀y∈t ¬(∃x ¬A(x) ∧ B(y)))^SH = ∀a ∃b (A_SH ∨₁ (b∀₁ [x] t B))
example (A B : Formula)
        (intA: SH_int_comp2 A (a,b,A_SH))
        (intB: SH_int_comp2 B (c,d,B_SH)) :
        SH_int_comp2 (b∀₁ y t (¬₁((∃₁ x (¬₁ A))∧₁B))) (x++a++g,b++c',((b∀₁ y t (A_SH ∨₁ ((b∃₁ c (c'.tt) (¬₁(B_SH)))).subst (HashMap.ofList (d.zip ((g.tt)⊙(c.tt)))) )))) :=
by
  --have hPrim := ex_2_2_PrimSymbb A B x y t
  rw [ex_2_2_PrimSymbb A B x y t]                                       -- ∀y∈t ¬ (∀x A(x) ∨ ¬B(y))
  have intForallA := @SH_int_comp2.unbForall A a b A_SH x intA             -- ∀x,a ∃b A_SH(x,a,b)
  have intNotB := @SH_int_comp2.neg B c d B_SH g c' intB                   -- ∀g ∃c' [∃ c c' ¬B_SH(c,gc)]
  have intOr := SH_int_comp2.disj intForallA intNotB                     -- ∀x,a,g ∃b,c' [A_SH(x,a,b) ∨ (∃ c c' ¬B_SH(c,gc))]
  --let Form := ((∀₁₁ x A).or B.not) -- b∀₁₁ y t
  let Form_SH := ((A_SH ∨₁ (b∃₁ c (c'.tt) (¬₁(B_SH)))).subst (d ⟹ (g.tt⊙c.tt)))
  exact @SH_int_comp2.bForall ((∀₁ x A).or B.not) (x++a++g) (b ++ c') (A_SH ∨₁ ((b∃₁ c (c'.tt) (¬₁(B_SH)))).subst (d ⟹ (g.tt⊙c.tt))) y t intOr







-- ---------------------------------------------------------------------
-- PROPOSITION 2.1 (p.46)
-- Interpretation of formulas with defined symbols.
-- ---------------------------------------------------------------------

-- Interpretation of A → B.

#check F_iff

-- VERSAO ERRADA
lemma SH_imp
  (A B : Formula)
  (intA : SH_int_comp A (a,b,A_SH)) (f a' : List String)
  (intB : SH_int_comp B (c,d,B_SH))
  (f a' : List String): SH_int_comp (A→₁B) (f++c, a'++d, ((b∀₁ a a'.tt (A_SH.subst (b ⟹ (f.tt⊙a.tt)))))→₁B_SH) :=
by
  unfold F_implies
  have intNotA := @SH_int_comp.neg A a b A_SH f a' intA
  have intForm := SH_int_comp.disj intNotA intB
  rw [bExistsTuple] at intForm
  rw [DoubleNeg] at intForm
  exact intForm

-- VERSAO CERTA
lemma SH_imp_corr     -- (A→B) = (¬A ∨ B)
  (A B : Formula)
  (intA : SH_int_comp2 A (a,b,A_SH)) (f a' : List String)
  (intB : SH_int_comp2 B (c,d,B_SH))
  (f a' : List String): SH_int_comp2 (A→₁B) (f++c, a'++d, ((((b∀₁ a a'.tt A_SH).subst (b ⟹ (f.tt⊙a.tt)))))→₁B_SH) :=
by
  unfold F_implies
  have intNotA := @SH_int_comp2.neg A a b A_SH f a' intA
  have intForm := SH_int_comp2.disj intNotA intB
  rw [bExistsTuple] at intForm
  rw [DoubleNeg] at intForm
  exact intForm

-- VERSAO CERTA COM NOTATION
lemma SH_imp_corr2     -- (A→B) = (¬A ∨ B)
  (A : Formula) {a b : List String} {A_SH : Formula}
  (intA : SH_int_comp2 A (a,b,A_SH))
  (B : Formula) {c d : List String} {B_SH : Formula}
  (intB : SH_int_comp2 B (c,d,B_SH))
  (f a' : List String): SH_int_comp2 (A→₁B) (f++c, a'++d, ((((b∀₁ a a'.tt A_SH).subst ((b ⟹ (f.tt⊙a.tt)))))→₁B_SH)) :=
by
  unfold F_implies
  have intNotA := @SH_int_comp2.neg A a b A_SH f a' intA
  have intForm := SH_int_comp2.disj intNotA intB
  rw [bExistsTuple] at intForm
  rw [DoubleNeg] at intForm
  exact intForm

#check SH_imp_corr2

-- -----------------------

-- Interpretation of A ∧ B.

-- VERSÃO CERTA
-- Damos as infos sobre A e depois as infos sobre B
lemma SH_and              -- (A∧₁B) = ¬((¬A) ∨ (¬B))
  (A : Formula) (a b : List String) (A_SH : Formula)
  (intA : SH_int_comp2 A (a,b,A_SH)) (f a' f' Φ : List String)
  (B : Formula) (c d : List String) (B_SH : Formula)
  (intB : SH_int_comp2 B (c,d,B_SH)) (g c' g' Ψ : List String):
  SH_int_comp2 (A∧₁B)
  (Φ++Ψ, f'++g',
  (b∃₁ (f++g) (f'++g').tt ( (((b∀₁ a a'.tt A_SH)).subst (b ⟹ (f.tt⊙a.tt)) ) ∧₁ (((b∀₁ c c'.tt B_SH)).subst (d ⟹ (g.tt⊙c.tt)) ) )).subst ((a'++c') ⟹ ((Φ++Ψ).tt⊙(f++g).tt))) :=
by
  unfold F_and
  rw [bExistsTuple]
  have intNotA := @SH_int_comp2.neg A a b A_SH f a' intA
  have intNotB := @SH_int_comp2.neg B c d B_SH g c' intB
  have intOr := SH_int_comp2.disj intNotA intNotB
  have intForm := @SH_int_comp2.neg ((¬₁A)∨₁(¬₁B)) (f++g) (a'++c') ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt) ∨₁ (b∃₁ c c'.tt (¬₁B_SH)).subst (d⟹g.tt⊙c.tt)) (Φ++Ψ) (f'++g') intOr
  rw [bExistsTuple, bExistsTuple, bExistsTuple, DoubleNeg, DoubleNeg, DoubleNeg] at intForm
  rw [DoubleNeg]
  exact intForm

#check SH_and

-- --------------------------
-- LEMA PARA TESTAR negação com tuplos de tamanhos diferentes, cenas com ∃x₁∈t₁ ∃x₂∈t₂
lemma TesteTuplos
  (A:Formula)
  (a a₁ a₂ b : String)
  (H : SH_int_comp A ([a₁, a₂],[b],A_SH)) :
  (SH_int_comp (¬₁A) (B,[a₁',a₂'],(b∃₁ [a₁, a₂] [a₁',a₂'].tt (¬₁(A_SH.subst (HashMap.ofList ([b].zip ((B.tt)⊙([a₁,a₂].tt))))))))) :=
by
  exact @SH_int_comp.neg A [a₁,a₂] [b] A_SH B [a₁',a₂'] H

lemma TesteTuplos2
  (A:Formula)
  (a a₁ a₂ b : List String)
  (H : SH_int_comp A (a₁++a₂,b,A_SH)) :
  (SH_int_comp (¬₁A) (B,a₁'++a₂',(b∃₁ (a₁++a₂) (a₁'++a₂').tt (¬₁(A_SH.subst (HashMap.ofList (b.zip ((B.tt)⊙((a₁++a₂).tt))))))))) :=
by
  exact @SH_int_comp.neg A (a₁++a₂) b A_SH B (a₁'++a₂') H

-- -------------------------------------

-- Interpretation of ∃x A(x).

-- VERSÃO CERTA
lemma SH_unbExists
  (A : Formula)
  (intA : SH_int_comp2 A (a,b,A_SH)) (a' f f' Φ : List String) (x x' : List String):
  SH_int_comp2 (∃₁ x A) (Φ, x'++f', ((b∃₁ (x++f) (x'++f').tt ((b∀₁ a (a'.tt) A_SH).subst (b⟹f.tt⊙a.tt))).subst (a' ⟹ ((Φ.tt)⊙((x++f).tt))))) :=
by
  unfold unbExistsTuple
  have intNot := @SH_int_comp2.neg A a b A_SH f a' intA
  have intForall := @SH_int_comp2.unbForall (¬₁A) f a' ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)) x intNot
  have intForm := @SH_int_comp2.neg (∀₁ x (¬₁A)) (x++f) a' ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)) Φ (x'++f') intForall
  rw [bExistsTuple, bExistsTuple] at intForm
  rw [DoubleNeg, DoubleNeg] at intForm
  rw [bExistsTuple]
  exact intForm

-- -------------------------------------

-- Interpretation of ∃x∈t A(x).

-- VERSAO CERTA
lemma SH_bExists
  (A : Formula) (a b : List String) (A_SH : Formula)
  (intA : SH_int_comp2 A (a,b,A_SH))  (f a' f' Φ : List String) (x : List String) (t : List Term):
  SH_int_comp2 (b∃₁ x t A) (Φ, f', ((b∃₁ f (f'.tt) ((b∃₁ x t ((b∀₁ a (a'.tt) A_SH).subst (b ⟹ (f.tt⊙a.tt)) )))).subst (a' ⟹ (Φ.tt⊙f.tt)))) :=
by
  unfold bExistsTuple
  have intNot := @SH_int_comp2.neg A a b A_SH f a' intA
  have intbForall := @SH_int_comp2.bForall (¬₁ A) f a' ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)) x t intNot
  have intForm := @SH_int_comp2.neg (b∀₁ x t (¬₁A)) f a' (b∀₁ x t ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))) Φ f' intbForall
  rw [bExistsTuple, bExistsTuple] at intForm
  rw [DoubleNeg, DoubleNeg] at intForm
  rw [DoubleNeg]
  exact intForm

-- ---------------------------------------------------------------------
-- REMARK 2.4 (p.43)
-- Interpretations with empty tuples
-- ---------------------------------------------------------------------

/-
example (A B C : Formula)
        (intA: SH_int_comp A (a,b,A_SH))
        (intB: SH_int_comp B (a,[],B_SH))
        (intC: SH_int_comp C ([],b,C_SH)):
-/

#check app_empty_list_fst

-- TBD: stuck at empty
example (B : Formula)
        (intB: SH_int_comp2 B (a,[],B_SH)):
        SH_int_comp2 (¬₁ B) ([],a',(b∃₁ a (a'.tt) ((¬₁B_SH)))) :=
by
  have intNot := @SH_int_comp2.neg B a [] B_SH [] a' intB
  simp
  rw [bExistsTuple, with_t] at intNot
  rw [DoubleNeg] at intNot
  --have H := app_empty_list_fst List.nil (a.tt)
  simp [HashMap.ofList] at intNot
  --simp [HashMap.empty] at intNot

  --simp [mkHashMap] at intNot
  --have H := app_empty_list_fst ([].tt) (a.tt)
  --have H := app_empty_list_fst List.nil (a.tt)
  --rw [app_empty_list_fst ([].tt) (a.tt)] at hA
  sorry

-- TBD: stuck at empty
example (C : Formula)
        (intC: SH_int_comp2 C ([],b,C_SH)):
        SH_int_comp2 (¬₁ C) (b,[],(¬₁C_SH)) :=
by
  have intNot := @SH_int_comp2.neg C [] b C_SH b [] intC
  rw [bExistsTuple, with_t] at intNot
  rw [DoubleNeg, HashMap.ofList] at intNot
  --simp [HashMap.ofList] at intNot
  sorry
  --rw [app_empty_list_fst (b.tt) []] at hA











-- --------------------------------------------------------
-- --------------------------------------------------------
-- --------------------------------------------------------

-- ------------------------------------------------
-- COMPUTAR SH INTERPRETATION COM OUTPUT DE FORMULA
-- ------------------------------------------------

def SH_int_base_rec (A:Formula) (H: isBase A): Formula := (Recreate ([], [], A))
def SH_int_base_comp (A:Formula) (H: isBase A): (List String × List String × Formula) := ([], [], A)

def SH_int_or_rec (A B : Formula)
  (hIntA: SH_int2 A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components)
  (hIntB: SH_int2 B BuSH) (hBcomp: (c,d,B_SH) = BuSH.components): Formula :=
  Recreate (a++c, b++d, (A_SH ∨₁ B_SH))

def SH_int_or_comp (A B : Formula)
  (hIntA: SH_int2 A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components)
  (hIntB: SH_int2 B BuSH) (hBcomp: (c,d,B_SH) = BuSH.components): (List String × List String × Formula) :=
  (a++c, b++d, (A_SH ∨₁ B_SH))

def SH_int_unbForall_rec (A : Formula) (x : List String)
  (hIntA: SH_int2 A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components): Formula :=
  Recreate (a++x, b, A_SH)

def SH_int_unbForall_comp (A : Formula) (x : List String)
  (hIntA: SH_int2 A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components): (List String × List String × Formula) :=
  (a++x, b, A_SH)

def SH_int_bForall_rec (A : Formula) (x : List String) (t : List Term)
  (hIntA: SH_int2 A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components): Formula :=
  Recreate (a, b, b∀₁ x t A_SH)

def SH_int_bForall_comp (A : Formula) (x : List String) (t : List Term)
  (hIntA: SH_int2 A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components): (List String × List String × Formula) :=
  (a, b, b∀₁ x t A_SH)

def SH_int_not_rec (A : Formula) {f a' : List String}
  (hIntA: SH_int2 A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components): Formula :=
  Recreate (f,a',(b∀₁ a (a'.tt) (¬₁(A_SH.subst (HashMap.ofList  (b.zip ((f.tt)⊙(a.tt))))))))

-- ---------------------------------------------------------

-- EXAMPLE:

open isAtomic
open isBase
def formulinha : Formula := (var "x") =₁ (var "y")
lemma lemazinho (x y : String) : isBase ((var x) =₁ (var y)) := by exact b_atom (isAtomic.at_eq (var x) (var y))

def Testinho := SH_int_base_rec ((var "x") =₁ (var "y")) (lemazinho "x" "y")
lemma lemazinho_testinho :
  ((SH_int_base_rec ((var "x") =₁ (var "y")) (lemazinho "x" "y")) = ((var "x") =₁ (var "y"))) := by
  sorry

#eval Testinho
#check DoubleNeg Testinho

-- ---------------------------------------------------------

-- LEMMA: If A is base and A = B, then B must be base

lemma baseEquality (A B:Formula) (hA : isBase A) (hEq : B = A) : isBase B := by
  rw [hEq]
  exact hA

-- ---------------------------------------------------------

-- Example: A ∨ (∀x∈t B)
-- example (A:Formula) (hInt : SH_int2 A AuSH) → (hComp : (a,b,A_SH) = AuSH.components2) :

example (A B:Formula) (H : SH_int2 (A→₁B) IMPuSH) {f a' :List String}:
  (isBase A_SH) → (SH_int2 A AuSH) → ((a,b,A_SH) = AuSH.components) →
  (isBase B_SH) → (SH_int2 B BuSH) → ((c,d,B_SH) = AuSH.components) →
  ((IMPuSH.components = (f++c,a'++d,(A_SH →₁ B_SH)))) := by sorry

/-


-- Vamos mostrar que se A^SH = ∀a ∃b A_SH e B^SH = ∀c B_SH que (A∨B)^SH = ∀a,c ∃b (A_SH ∨ B_SH)


-- --------------------------------------------------------
-- --------------------------------------------------------
-- --------------------------------------------------------



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
#check (exAA xx yy FormulaF).components
#eval (exAA xx yy FormulaF).components

#eval (∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y")))              -- Formula ∀ "x" ∃ "y" (x=y)
#eval (∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components  -- yes
#eval (∀₁ ["x"] (var "x" =₁ var "y")).components             -- yes
#eval (∃₁ ["y"] (var "x" =₁ var "y")).components             -- yes

#eval Recreate ((∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components)  -- yes
#eval RecreateSimp ((∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components)  -- yes


--theorem Soundness (A : Formula) (hA1 : SH_int2 A AuSH) (hA2 : AuSH.components2 = (a,b,A_SH)) (hA3 : isBase A_SH):
-- (insert (bAC x y f B) ∅ ⊢ A) → (∃(t: List Term), (Provable (∀₁ a (A_SH.subst (HashMap.ofList (b.zip ((f.tt)⊙(a.tt)))))))) := by sorry    -- TBD: falta subst aqui


/- Next tarefas:
    1. Pôr namespaces para os exemplos:
        a) No FOLanguage
        b) Axioms / FiniteTypes / Syntax / ResultsAndOtherDefinitions
    2. Resolver isBase como hipotese em components... done?
    3. Resolver Term.application para tuples -> Notation 1.4
-/



-- --------------------------------------------------------
-- --------------------------------------------------------
-- --------------------------------------------------------



-- mover
open Axioms

example : Formula.components (AxiomE1_matrix "x") = ([], [], (AxiomE1_matrix "x")) := by
  exact rfl

example : (AxiomE2_matrix x₁ x₂ A hA).components = ([], [], (AxiomE2_matrix x₁ x₂ A hA)) := by sorry


#eval (AxiomE1_matrix "x").components
-- Quero mostrar que pôr foralls antes dos axiomas, que não muda nada
-- que SH_int2 de axiomE1 que é a mesma coisa que SH_int2 de AxiomE1
--#eval
#eval (AxiomE1 "x").components
--#eval SH_int2 (AxiomE1 "x")
