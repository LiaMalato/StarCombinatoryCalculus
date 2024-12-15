import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.Axioms
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Sigma
import Mathlib.Data.List.Basic
import Batteries

open Term
open Formula
open Batteries

-- -------------------------------------------------------------
-- -------------------------------------------------------------
--          SHOENFIELD'S FUNCTIONAL INTERPRETATION
--         (SECTION 2.2: A herbrandized version of
--          Shoenfield's functional interpretation)
-- -------------------------------------------------------------
-- -------------------------------------------------------------

/- FILE DESCRIPTION:
In this file we discuss Shoenfield's functional interpretation.
The file corresponds to pages 35 to 44.
-/

-- -------------------------------------------------------------
-- DEFINITION 2.1 (p.38):
-- Shoenfield's functional interpretation
-- -------------------------------------------------------------

/-
To define Shoenfield's functional interpretation we need some auxiliary functions to deal with the
different components of the interpretation of a formula. Every interpretation has a list of universal
variables, a list of existential variables and the matrix, i.e. the lower SH-formula (a base formula).
These three components will be represented by a triple.

For example, if a formula A has the interpretation A^SH given by
                        ∀a ∃b A_SH(a,b)
then we would represent this as (a,b,A_SH).

The function 'components' transforms a formula such as ∀a ∃b A_SH(a,b) into the tupe (a,b,A_SH).
The function 'Recreate' transforms a tuple such as (a,b,A_SH) into the formula ∀a ∃b A_SH(a,b).

Shoenfield's functional interpretation is given by the inductive definition SH_int (defined later in
this file).
-/

-- --------------------------------
-- COMPONENTS OF AN INTERPRETATION
-- --------------------------------

/- When having an interpretation, then components decomposes it into the universal variables,
the existential variables and the matrices.
Components can only be applied to formulas of the form ∀a ∃b A.-/

def Formula.components : Formula → (List String × List String × Formula)
| unbForall x A =>
    let (a, b, rest) := A.components
    ([x]++a, b, rest)
| not (unbForall x A) =>
    let (a, b, rest) := A.components
    (b, [x]++a, not rest)
| not (not A) =>                            -- This handles the double negation case
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
| A => ([], [], A)

-- --------
-- EXAMPLE: how to use components with the formula ∀x ∃y,z ¬A
-- --------

def ex_formula_comp1 (A:Formula) : Formula := (∀₁₁ "x" (∃₁₁ "y" (∃₁₁ "z" (¬₁A))))

-- EXAMPLE 1:
#eval (ex_formula_comp1 (Formula.rel "R" [var_x,var_y])).components               -- Output: ([x], [y, z], ¬₁R(x,y))

-- EXAMPLE 2: components of
#eval components (∀₁₁ "x" (¬₁(∀₁₁ "y" (rel "P" [var_x, var_y]))))                 -- Output: ([x], [y, z], ¬₁R(x,y))

-- EXAMPLE 3:
#eval components (∀₁₁ "x" ((∃₁₁ "y" (¬₁(rel "P" [var_x, var_y])))))               -- Output: ([x], [y, z], ¬₁R(x,y))

-- EXAMPLE 4:
def ex_formula_comp2 : Formula :=
  ∀₁ ["x"] (¬₁ (b∀₁₁ "y" (Term.var "t") (Formula.rel "R" [var "y"])))
#eval ex_formula_comp2.components                                                 -- Output: (["x"], [], ∀y∈t R[y])


-- --------------------------------
-- RECREATE
-- --------------------------------

-- Recreate takes in a triplet of the form (a,b, A) and outputs the formula ∀a∃b A.
-- To be applied to formulas that have been interpreted previously.

@[simp]
def Recreate : (List String × List String × Formula) → Formula
| ([], [], rest) => rest
| (a, [], rest) => ∀₁ a rest
| ([], b, rest) => ∃₁ b rest
| (a, b, rest) => ∀₁ a (∃₁ b rest)

-- EXAMPLE:
#eval (∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y")))             -- Formula ∀x ∃y (x=y)
#eval (∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components  -- Components of ∀x ∃y (x=y)
#eval (∀₁ ["x"] (var "x" =₁ var "y")).components             -- Components of ∀x (x=y)
#eval (∃₁ ["y"] (var "x" =₁ var "y")).components             -- Components of ∃y (x=y)

#eval Recreate ((∀₁ ["x"] (∃₁ ["y"] (var "x" =₁ var "y"))).components)  -- Using Recreate and components


-- --------------------------------------------------------------------
-- DEFINITION 2.1 (p.38):
-- Shoenfield's functional interpretation
-- --------------------------------------------------------------------

-- --------------------------------
-- TECHNICALITIES
-- --------------------------------

-- NOTATION: Instead of writing 'HashMap.ofList (x.zip t)', we adopt the notation 'x⟹t'
@[simp]
def with_t (x : List String) (t : List Term) := HashMap.ofList (x.zip t)

notation x "⟹" t => with_t x t

-- DISJOINT LISTS OF VARIABLES:

-- Two disjoint lists
def disj_lists_two (ls1 ls2 : List String) : Prop :=
  ∀ x, x ∈ ls1 → x ∉ ls2

-- Four disjoint lists
def disj_lists_four (l1 l2 l3 l4 : List String) : Prop :=
  disj_lists_two l1 l2 ∧ disj_lists_two l1 l3 ∧ disj_lists_two l1 l4 ∧
  disj_lists_two l2 l3 ∧ disj_lists_two l2 l4 ∧ disj_lists_two l3 l4


-- --------------------------------------
-- SHOENFIELD'S FUNCTIONAL INTERPRETATION
-- --------------------------------------

-- To define Shoenfield's functional interpretation we will use a triple as described above.
-- We assume A^SH = ∀a ∃b A_SH(a,b) and B^SH = ∀c ∃d B_SH(c,d)

-- DEFINITION 2.1 (p.36): Shoenfield's functional interpretation
inductive SH_int : Formula → (List String × List String × Formula) → Prop
| base : (h : isBase A) → (SH_int A ([],[],A))            -- Interpretation of base formulas
| disj : (h : disj_lists_four a b c d) →                  -- Interpretation of a disjunction
         SH_int A (a,b,A_SH) →                               -- (A∨B)^SH = ∀a,c ∃b,d [ A_SH(a,b) ∨ B_SH(c,d) ]
         SH_int B (c,d,B_SH) →
         SH_int (A∨₁B) (a++c,b++d,(A_SH ∨₁ B_SH))
| neg {f a': List String}:                                -- Interpretation of a negation
        (h : disj_lists_two a b) →                           -- (¬A)^SH = ∀f ∃a' [ ∃a∈a' A_SH(a,fa) ]
        SH_int A (a,b,A_SH) →
        SH_int (¬₁A) (f,a',     (b∃₁ a (a'.tt) (¬₁A_SH)).subst (b ⟹ ((f.tt)⊙(a.tt)))      )
| unbForall : (h : disj_lists_two a b) →                  -- Interpretation of an unbounded universal quantification
              SH_int A (a,b,A_SH) →                          -- (∀x A)^SH = ∀x,a ∃b [ A_SH(x,a,b) ]
              SH_int (∀₁ x A) (x++a,b,A_SH)
| bForall : (h : disj_lists_two a b) →                    -- Interpretation of an bounded universal quantification
            SH_int A (a,b,A_SH) →                            -- (∀x∈t A(x))^SH = ∀a ∃b [ ∀x∈t A_SH(x,a,b) ]
            SH_int (b∀₁ x t A) (a,b,(b∀₁ x t A_SH))

-- HELPER DEFINITION:
inductive SH_intp : Formula → (List String × List String × Formula) → Prop
| base : (h : isBase A) → (SH_intp A ([],[],A))
| disj : SH_intp A (a,b,A_SH) →
         SH_intp B (c,d,B_SH) →
         SH_intp (A∨₁B) (a++c,b++d,(A_SH ∨₁ B_SH))
| neg {f a': List String}:
        SH_intp A (a,b,A_SH) →
        SH_intp (¬₁A) (f,a',     (b∃₁ a (a'.tt) (¬₁A_SH)).subst (b ⟹ ((f.tt)⊙(a.tt)))      )
| unbForall : SH_intp A (a,b,A_SH) →
              SH_intp (∀₁ x A) (x++a,b,A_SH)
| bForall : SH_intp A (a,b,A_SH) →
            SH_intp (b∀₁ x t A) (a,b,(b∀₁ x t A_SH))

-- DEFINITION: Shoenfield's functional interpretation if we wish to automatically retrieve the formula instead of the triple
inductive SH_int_form : Formula → Formula → Prop
| base : (h : isBase A) → (SH_int_form A A)
| disj : SH_int_form A AuSH →
         SH_int_form B BuSH →
         AuSH.components = (a,b,A_SH) →
         BuSH.components = (c,d,B_SH) →
         (SH_int_form (A∨₁B) (Recreate (a++c,b++d,(A_SH ∨₁ B_SH))))
| neg {f a': List String}:
        SH_int_form A AuSH →
        (a,b,A_SH) = AuSH.components →
        (SH_int_form (¬₁A) (Recreate (f,a',(b∃₁ a (a'.tt) (¬₁(A_SH.subst (HashMap.ofList  (b.zip ((f.tt)⊙(a.tt))))))))))
| unbForall : SH_int_form A AuSH →
              AuSH.components = (a,b,A_SH) →
              (SH_int_form (∀₁₁ x A) (Recreate (a++[x],b,A_SH)))
| bForall : SH_int_form A AuSH →
            AuSH.components = (a,b,A_SH) →
            (SH_int_form (b∀₁ x t A) (Recreate (a,b,(b∀₁ x t A_SH))))


-- --------------------------------
-- TECHNICALITIES:
-- Extracting tuples from assumptions on Shoenfield's functional interpretation.
-- --------------------------------

inductive SH_int_type : Type
| mk : List String → List String → Formula → SH_int_type

def SH_int_Comp : SH_int_type → (List String × List String × Formula)
| SH_int_type.mk a b A_SH => (a, b, A_SH)

def extract_tuple {A : Formula} {a b a' f : List String} {A_SH : Formula}
  (hA : SH_intp A (a, b, A_SH)) (hB : SH_intp B (c, d, B_SH)) : (List String × List String × Formula) :=
  match A with
  | (.or A B)           => (a++c, b++d, A)
  | (.not A)            => (f,a',((b∃₁ a (a'.tt) (¬₁(A_SH))).subst (b ⟹ ((f.tt)⊙(a.tt)))))
  | (.unbForall x A)    => (a++[x],b,A_SH)
  | (.bForall x t A)    => (a,b,(b∀₁₁ x t A_SH))
  | A                   => ([],[],A)

def extract_tuple_base {A: Formula} (hA : isBase A)
  (hAint : SH_intp A ([], [], A)) : (List String × List String × Formula) :=
  ([], [], A)


-- --------------------------------------------------------------
-- EXAMPLE 2.1 (p.37):
-- Interpretation of (A ∨ (∀x∈t B(x))), with B(x) a base formula.
-- --------------------------------------------------------------

-- AUXILLIARY LEMMA (technicality):
-- Having two equal lists tl1 and tl2, we can add a first element h without changing the equality between the lists,
-- i.e. if [a₁ ,..., aₙ]=[b₁ ,..., bₙ], then [h,a₁ ,..., aₙ]=[h,b₁ ,..., bₙ].
lemma List.cons_eq (head:A) (tl1 tl2: List A) : tl1 = tl2 → h :: tl1 = h :: tl2 := by sorry

-- AUXILLIARY LEMMA (technicality):
-- The union between a list l and the empty list [] is the list l.
@[simp]
lemma List.union_nil (l : List String): l ∪ [] = l := by sorry

-- PRELIMINARY EXAMPLE:
-- Showing that (∀₁₁ x A)^SH = ∀ a,x ∃ b A_SH.
example (h: SH_intp A (a,b,A_SH)) :
        SH_intp (∀₁ x A) (x++a,b,A_SH) :=
by
  exact @SH_intp.unbForall A a b A_SH x h

-- EXAMPLE 2.1 (p.37): (A ∨ (∀x∈t B(x)))^SH = ∀a ∃b (A_SH ∨₁ (b∀₁ [x] t B))
example (A B : Formula) (hA: SH_intp A (a,b,A_SH)) (hB : isBase B) :
        SH_intp (A ∨₁ (b∀₁ [x] t B)) (a,b,(A_SH ∨₁ (b∀₁ [x] t B))) :=
by
  have intB := SH_intp.base hB                                                             -- B
  have intForall := @SH_intp.bForall B [] [] B [x] t intB                                  -- ∀x∈t B(x)
  have intOr := @SH_intp.disj A a b A_SH (b∀₁ [x] t B) [] [] (b∀₁ [x] t B) hA intForall    -- A_SH ∨ ∀x∈t B(x)
  have Ha := a.append_nil
  have Hb := b.append_nil
  rw [Ha,Hb] at intOr                                                                      -- simplifies the result by using hypothesis Ha and Hb
  exact intOr


-- ---------------------------------------------------------------------
-- EXAMPLE 2.2 (p.37):
-- Interpretation of ∀y∈t ¬(∃x ¬A(x) ∧ B(y)).
-- ---------------------------------------------------------------------

-- PRELIMINARY EXAMPLE:
lemma ex_2_2_PrimSymbb (A B : Formula) (x y : List String) (t : List Term) : (b∀₁ y t (¬₁((∃₁ x (¬₁A))∧₁B))) = (b∀₁ y t ((∀₁ x A)∨₁(¬₁B))) :=
by
  rw [DeMorgan_and (∃₁ x (¬₁A)) B]
  unfold unbExistsTuple
  rw [DoubleNeg, DoubleNeg]

-- EXAMPLE 2.2: (∀y∈t ¬(∃x ¬A(x) ∧ B(y)))^SH = ∀a ∃b (A_SH ∨₁ (b∀₁ [x] t B))
example (A B : Formula)
        (intA: SH_intp A (a,b,A_SH))
        (intB: SH_intp B (c,d,B_SH)) :
        SH_intp (b∀₁ y t (¬₁((∃₁ x (¬₁ A))∧₁B))) (x++a++g,b++c',((b∀₁ y t (A_SH ∨₁ ((b∃₁ c (c'.tt) (¬₁(B_SH)))).subst (HashMap.ofList (d.zip ((g.tt)⊙(c.tt)))) )))) :=
by
  rw [ex_2_2_PrimSymbb A B x y t]                                           -- ∀y∈t ¬ (∀x A(x) ∨ ¬B(y))
  have intForallA := @SH_intp.unbForall A a b A_SH x intA                   -- ∀x,a ∃b A_SH(x,a,b)
  have intNotB := @SH_intp.neg B c d B_SH g c' intB                         -- ∀g ∃c' [∃ c c' ¬B_SH(c,gc)]
  have intOr := SH_intp.disj intForallA intNotB                             -- ∀x,a,g ∃b,c' [A_SH(x,a,b) ∨ (∃ c c' ¬B_SH(c,gc))]
  exact @SH_intp.bForall ((∀₁ x A).or B.not) (x++a++g) (b ++ c') (A_SH ∨₁ ((b∃₁ c (c'.tt) (¬₁(B_SH)))).subst (d ⟹ (g.tt⊙c.tt))) y t intOr


-- ---------------------------------------------------------------------
-- PROPOSITION 2.1 (p.41):
-- Interpretation of formulas with defined symbols.
-- ---------------------------------------------------------------------

-- Interpretation of A → B.

-- PROPOSITION 2.1 a): Interpretation of A → B.
lemma SH_imp
  (A B : Formula)
  (intA : SH_intp A (a,b,A_SH)) (f a' : List String)
  (intB : SH_intp B (c,d,B_SH))
  (f a' : List String): SH_intp (A→₁B) (f++c, a'++d, ((((b∀₁ a a'.tt A_SH).subst (b ⟹ (f.tt⊙a.tt)))))→₁B_SH) :=
by
  unfold F_implies                                           -- (A→B) = (¬A ∨ B)
  have intNotA := @SH_intp.neg A a b A_SH f a' intA
  have intForm := SH_intp.disj intNotA intB
  rw [bExistsTuple] at intForm
  rw [DoubleNeg] at intForm
  exact intForm

-- PROPOSITION 2.1 b): Interpretation of A ∧ B.
lemma SH_and
  (A : Formula) (a b : List String) (A_SH : Formula)
  (intA : SH_intp A (a,b,A_SH)) (f a' f' Φ : List String)
  (B : Formula) (c d : List String) (B_SH : Formula)
  (intB : SH_intp B (c,d,B_SH)) (g c' g' Ψ : List String):
  SH_intp (A∧₁B)
  (Φ++Ψ, f'++g',
  (b∃₁ (f++g) (f'++g').tt ( (((b∀₁ a a'.tt A_SH)).subst (b ⟹ (f.tt⊙a.tt)) ) ∧₁ (((b∀₁ c c'.tt B_SH)).subst (d ⟹ (g.tt⊙c.tt)) ) )).subst ((a'++c') ⟹ ((Φ++Ψ).tt⊙(f++g).tt))) :=
by
  unfold F_and                                                -- (A∧₁B) = ¬((¬A) ∨ (¬B))
  rw [bExistsTuple]
  have intNotA := @SH_intp.neg A a b A_SH f a' intA
  have intNotB := @SH_intp.neg B c d B_SH g c' intB
  have intOr := SH_intp.disj intNotA intNotB
  have intForm := @SH_intp.neg ((¬₁A)∨₁(¬₁B)) (f++g) (a'++c') ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt) ∨₁ (b∃₁ c c'.tt (¬₁B_SH)).subst (d⟹g.tt⊙c.tt)) (Φ++Ψ) (f'++g') intOr
  rw [bExistsTuple, bExistsTuple, bExistsTuple, DoubleNeg, DoubleNeg, DoubleNeg] at intForm
  rw [DoubleNeg]
  exact intForm

-- PROPOSITION 2.1 c): Interpretation of ∃x A(x).
lemma SH_unbExists
  (A : Formula)
  (intA : SH_intp A (a,b,A_SH)) (a' f f' Φ : List String) (x x' : List String):
  SH_intp (∃₁ x A) (Φ, x'++f', ((b∃₁ (x++f) (x'++f').tt ((b∀₁ a (a'.tt) A_SH).subst (b⟹f.tt⊙a.tt))).subst (a' ⟹ ((Φ.tt)⊙((x++f).tt))))) :=
by
  unfold unbExistsTuple
  have intNot := @SH_intp.neg A a b A_SH f a' intA
  have intForall := @SH_intp.unbForall (¬₁A) f a' ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)) x intNot
  have intForm := @SH_intp.neg (∀₁ x (¬₁A)) (x++f) a' ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)) Φ (x'++f') intForall
  rw [bExistsTuple, bExistsTuple] at intForm
  rw [DoubleNeg, DoubleNeg] at intForm
  rw [bExistsTuple]
  exact intForm

-- PROPOSITION 2.1 d): Interpretation of ∃x∈t A(x).
lemma SH_bExists
  (A : Formula) (a b : List String) (A_SH : Formula)
  (intA : SH_intp A (a,b,A_SH))  (f a' f' Φ : List String) (x : List String) (t : List Term):
  SH_intp (b∃₁ x t A) (Φ, f', ((b∃₁ f (f'.tt) ((b∃₁ x t ((b∀₁ a (a'.tt) A_SH).subst (b ⟹ (f.tt⊙a.tt)) )))).subst (a' ⟹ (Φ.tt⊙f.tt)))) :=
by
  unfold bExistsTuple
  have intNot := @SH_intp.neg A a b A_SH f a' intA
  have intbForall := @SH_intp.bForall (¬₁ A) f a' ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt)) x t intNot
  have intForm := @SH_intp.neg (b∀₁ x t (¬₁A)) f a' (b∀₁ x t ((b∃₁ a a'.tt (¬₁A_SH)).subst (b⟹f.tt⊙a.tt))) Φ f' intbForall
  rw [bExistsTuple, bExistsTuple] at intForm
  rw [DoubleNeg, DoubleNeg] at intForm
  rw [DoubleNeg]
  exact intForm


-- ---------------------------------------------------
-- TECHNICALITIES:
-- Results to deal with empty hashmaps and empty lists
-- ---------------------------------------------------

@[simp]
lemma Formula.subst_empty (A: Formula) : A.subst HashMap.empty = A := by sorry

lemma Subst_empty_empty (A : Formula) : (A.subst ([]⟹[])) = A :=
by
  rw [with_t]
  rw [HashMap.ofList]
  simp [List.foldl]

lemma Subst_with_empty (A:Formula) (x:String) :
  A.subst ([]⟹[].tt⊙([x].tt)) = A :=
by
  simp [Subst_empty_empty]
  rw [HashMap.ofList, List.foldl]
  exact (Formula.subst_empty A)

lemma Subst_with_empty_tuple (A:Formula) (x:  List String) :
  A.subst ([]⟹[].tt⊙(x.tt)) = A :=
by
  simp [Subst_empty_empty]
  sorry

lemma Subst_with_empty_tuple2 (A:Formula) (x:  List String) :
  A.subst (x⟹(([].tt)⊙(x.tt))) = A :=
by
  simp [Subst_empty_empty]
  sorry
  --unfold with_t
  --simp [HashMap.ofList]

lemma Subst_with_empty_tuple3 (A:Formula) (x:  List String) :
  A.subst (x⟹((x.tt)⊙([].tt))) = A :=
by
  simp [Subst_empty_empty]
  sorry
  --unfold with_t
  --simp [HashMap.ofList]

lemma Subst_with_empty_tuple4 (A:Formula) (x:  List String) :
  A.subst (x⟹(([].tt)⊙([].tt))) = A :=
by
  simp [Subst_empty_empty]
  sorry
  --unfold with_t
  --simp [HashMap.ofList]

lemma app_empty_listss : ((([].tt)⊙([].tt))) = [] :=
by
  --unfold TermTupleApp_list
  --rw [List.foldr]
  --rw [TermTupleApp_list]
  sorry

lemma app_empty_list_secc (x : List String) : (((x.tt)⊙([].tt)) = []) :=
by
  induction x
  case nil =>
    --rw [app_empty_lists]
    sorry
  case cons _ _ _ =>
    simp

-- ---------------
-- OTHER EXAMPLES: interpretations of formulas
-- ---------------

-- EXAMPLE 1:
example (B : Formula)
        (intB: SH_intp B (a,[],B_SH)):
        SH_intp (¬₁ B) ([],a',((b∃₁ a (a'.tt) ((¬₁B_SH))).subst ([] ⟹ (([].tt)⊙(a.tt))))) :=
by
  exact @SH_intp.neg B a [] B_SH [] a' intB


-- EXAMPLE 2:
example (C C_SH : Formula)
        (intC: SH_intp C ([],b,C_SH)):
        SH_intp (¬₁ C) (b,[],((¬₁C_SH).subst (b ⟹ ([].tt⊙[].tt)))) :=
by
  have intNot := @SH_intp.neg C [] b C_SH b [] intC
  rw [bExistsTuple] at intNot
  rw [DoubleNeg] at intNot
  rw [bForallTuple_nil] at intNot
  have H1 := Subst_with_empty_tuple3 C_SH.not b
  rw [H1] at intNot
  have H2 := Subst_with_empty_tuple4 C_SH.not b
  rw [H2]
  exact intNot


-- ---------------------------------------------------------------------
-- REMARK 2.6 (p.48)
-- Interpretation of ∃xA(x) with A base
-- ---------------------------------------------------------------------

example (A : Formula)
        (hAbase : isBase A) (x x' : List String) :
        (SH_intp (∃₁ x A) ([],x',(b∃₁ x x'.tt A))) :=
by
  unfold unbExistsTuple
  have notA := isBase.b_not hAbase
  have intBase := SH_intp.base notA
  have intForall := @SH_intp.unbForall (¬₁A) [] [] (¬₁A) x intBase
  rw [x.append_nil] at intForall
  have intNot := @SH_intp.neg (∀₁ x (¬₁A)) x [] (¬₁A) [] x' intForall
  rw [DoubleNeg] at intNot
  have h := Subst_with_empty_tuple (b∃₁ x x'.tt A) x
  rw [h] at intNot
  exact intNot


-- ---------------------------------------------------------------------
--                            EXTRAS
-- ---------------------------------------------------------------------

-- -------------------------------------------------------------
-- ALTERNATIVE TO SH_INT
-- Computing the intepretation and obtaining a formula as output
-- -------------------------------------------------------------

-- DEFINITION: Interpretation of base formulas
def SH_int_base_rec (A:Formula) (H: isBase A): Formula := (Recreate ([], [], A))
def SH_int_base_comp (A:Formula) (H: isBase A): (List String × List String × Formula) := ([], [], A)

-- DEFINITION: Interpretation of a disjunction
def SH_int_or_rec (A B : Formula)
  (hIntA: SH_int_form A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components)
  (hIntB: SH_int_form B BuSH) (hBcomp: (c,d,B_SH) = BuSH.components): Formula :=
  Recreate (a++c, b++d, (A_SH ∨₁ B_SH))

def SH_int_or_comp (A B : Formula)
  (hIntA: SH_int_form A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components)
  (hIntB: SH_int_form B BuSH) (hBcomp: (c,d,B_SH) = BuSH.components): (List String × List String × Formula) :=
  (a++c, b++d, (A_SH ∨₁ B_SH))

-- DEFINITION: Interpretation of an unbounded universal quantification
def SH_int_unbForall_rec (A : Formula) (x : List String)
  (hIntA: SH_int_form A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components): Formula :=
  Recreate (a++x, b, A_SH)

def SH_int_unbForall_comp (A : Formula) (x : List String)
  (hIntA: SH_int_form A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components): (List String × List String × Formula) :=
  (a++x, b, A_SH)

-- DEFINITION: Interpretation of a bounded universal quantification
def SH_int_bForall_rec (A : Formula) (x : List String) (t : List Term)
  (hIntA: SH_int_form A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components): Formula :=
  Recreate (a, b, b∀₁ x t A_SH)

def SH_int_bForall_comp (A : Formula) (x : List String) (t : List Term)
  (hIntA: SH_int_form A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components): (List String × List String × Formula) :=
  (a, b, b∀₁ x t A_SH)

-- DEFINITION: Interpretation of a negation
def SH_int_not_rec (A : Formula) {f a' : List String}
  (hIntA: SH_int_form A AuSH) (hAcomp: (a,b,A_SH) = AuSH.components): Formula :=
  Recreate (f,a',(b∀₁ a (a'.tt) (¬₁(A_SH.subst (HashMap.ofList  (b.zip ((f.tt)⊙(a.tt))))))))

-- AUXILIARY LEMMA: If A is base and A = B, then B must be base
lemma baseEquality (A B:Formula) (hA : isBase A) (hEq : B = A) : isBase B := by
  rw [hEq]
  exact hA

-- ---------------------------------------
-- End of file
-- ---------------------------------------


-- ---------------------------------------
-- ---------------------------------------
--     EXTRAS (movers, in the making)
-- ---------------------------------------
-- ---------------------------------------

-- --------------------------------
-- DEFINITION:
-- The interpretation of a base formula is the base formula itself.
-- --------------------------------

-- DEFINITION: For formulas without universal and existential quantifiers, the lower SH formula is equal to the original formula.
@[simp]
def baseBase (A:Formula) (hA : isBase A) (hIntA: SH_int_form A AuSH) (hAcomp: AuSH.components = ({},{},A_SH))
  := A_SH = A

-- DEFINITION: If A is base, then the lower SH-formula is equal to A
@[simp]
def baseBase_comp (A:Formula) (hA : isBase A) (hIntA: SH_intp A ([],[],A_SH))
  := A_SH = A

-- DEFINITION: If A is base, then the interpretation of A is equal to A
@[simp]
def baseBase_rec (A:Formula) (hA : isBase A) (hIntA: SH_intp A ([],[],A_SH))
  := (Recreate ([],[],A_SH)) = A

-- --------------------------------

inductive SH_int_comp : Formula → (List String × List String × Formula) → Prop
| base : (h : isBase A) → (SH_int_comp A ([],[],A))
| disj : SH_int_comp A (a,b,A_SH) →
         SH_int_comp B (c,d,B_SH) →
         (SH_int_comp (A∨₁B) (a++c,b++d,(A_SH ∨₁ B_SH)))               -- (A∨B)^SH = ∀a,c ∃b,d [ A_SH(a,b) ∨ B_SH(c,d) ]
| neg {f a': List String}:
        SH_int_comp A (a,b,A_SH) →
        (SH_int_comp (¬₁A) (f,a',(b∃₁ a (a'.tt) (¬₁(A_SH.subst ((b ⟹ ((f.tt)⊙(a.tt)))))))))
| unbForall : SH_int_comp A (a,b,A_SH) →
              (SH_int_comp (∀₁₁ x A) ([x]++a,b,A_SH))                 -- (∀x A)^SH = ∀x,a ∃b [ A_SH(x,a,b) ]
| bForall : SH_int_comp A (a,b,A_SH) →
            (SH_int_comp (b∀₁ x t A) (a,b,(b∀₁ x t A_SH)))            -- (∀x∈t A(x))^SH = ∀a ∃b [ ∀x∈t A_SH(x,a,b) ]

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

open axioms

example : Formula.components (AxiomE1_matrix "x") = ([], [], (AxiomE1_matrix "x")) := by
  exact rfl

example : (AxiomE2_matrix x₁ x₂ A hA).components = ([], [], (AxiomE2_matrix x₁ x₂ A hA)) := by sorry

#eval (AxiomE1_matrix "x").components
#eval (AxiomE1 "x").components
--#eval SH_int_form (AxiomE1 "x")
