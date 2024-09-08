import MathLib.Tactic

-- Para import de dentro de um folder, escrever:
-- import LeanProjeto2.TestesAndOthers.Testes

-- --------------------
-- ------ FOL ---------
-- --------------------

/-
-- Definition: permite associar um conjunto de variáveis a um termo (para lidarmos com coisas como t(x) em axiomas, etc)
inductive L_closed_under_term : LTerm → Finset String → Prop
| Lcu_Lvar : x ∈ α → L_closed_under_term (Lvar x) α                   -- A variables (Lvar x) is closed under the set of variables α if x is an element of α.
| Lcu_Lconst : L_closed_under_term (Lconst c) α                       -- A constant (Lconst c) is closed under any set of variables α since constants do not contain any variables.
| Lcu_Lfunc :
    (∀ t, t ∈ ts → L_closed_under_term t α) →                         -- A function term (Lfunc f ts) is closed under α if every term t in the list ts is closed under α.
    L_closed_under_term (Lfunc f ts) α
-- TODO (future): tem de ser sempre o mesmo conjunto α? Em princípio cada t podia ter outro conjunto...
-/

/-
t1 : x=x
t2 : y=z
f(t1,t2)
-/


/-
-- Definition: permite associar um conjunto de variáveis a uma fórmula (para lidarmos com coisas como t(x) em axiomas, etc)
inductive L_closed_under_formula : LFormula → Finset String → Prop
| cu_atomic_L : ∀ (P : LPred) (ts : List LTerm) (α : Finset String),        -- An atomic formula atomic_L P ts is closed under a set α if all terms in the list ts are closed under α
    (∀ t, t ∈ ts → L_closed_under_term t α) →
    L_closed_under_formula (atomic_L P ts) α
| cu_not_L : ∀ (A : LFormula) (α : Finset String),                          -- ¬₀A is closed under a set α if A is closed under α.
    L_closed_under_formula A α →
    L_closed_under_formula (not_L A) α
| cu_or_L : ∀ (A B : LFormula) (α β : Finset String),                       -- A∨₀B is closed under a union of two sets α and β if A is closed under α and B is closed under β.
    L_closed_under_formula A α →
    L_closed_under_formula B β →
    L_closed_under_formula (or_L A B) (α ∪ β)
| cu_forall_L : ∀ (x : String) (A : LFormula) (α : Finset String),          -- ∀₀ x A is closed under a set α if A is closed under the set α with the variable x added to it.
    L_closed_under_formula A (α ∪ {x}) →
    L_closed_under_formula (forall_L x A) α      -- DONE: check this with the ∪ {x}

A(x)    x ∈ A.freevars
-/


-- --------------------------
-- ------ STAR LANG ---------
-- --------------------------

/-
-- Definition: permite associar um conjunto de variáveis a um termo (para lidarmos com coisas como t(x) em axiomas, etc)
inductive closed_under : Term → Finset String → Prop                      -- TODO: estas coisas em baixo é para tirar?
| cu_lcons : L_closed_under_term t α → closed_under (lcons t) α
| cu_pi : closed_under (pi) α                                             -- a tirar? Π não tem variáveis
| cu_sigma : closed_under (sigma) α                                       -- a tirar? Σ não tem variáveis
| cu_sing : closed_under (sing) α                                         -- a tirar? 𝔰 não tem variáveis
| cu_bUnion : closed_under (bUnion) α                                     -- a tirar? ∪ não tem variáveis
| cu_iUnion : closed_under (iUnion) α                                     -- a tirar? ind_U não tem variáveis
| cu_var :
    x ∈ α →
    -----------
    closed_under (var x) α
| cu_app : closed_under t₁ α → closed_under t₂ β → closed_under (app t₁ t₂) (α ∪ β)
-- TODO: o de cima ou | cu_app : closed_under t₁ α → closed_under t₂ α → closed_under (app t₁ t₂) α ?
-/

-- example (x:String) (α: Finset String) (h:{x : Term | x.closed_under α})
--   (y:Term) (h: y.closed_under α)
-- :
--    by sorry



-- -------------------------------------
-- FORMULA CLOSED UNDER
-- -------------------------------------

-- Definition: closed_under for formulas inStar
-- Cuidado: cada vez que temos um termo t ele pode ou não ser um LTerm => pattern matching
-- o que não acrescenta novas coisas => universally closed under any set of variables

/-
-- operations or constants that are closed under any set of variables.
inductive closed_under_formula : Formula → Finset String → Prop

| cu_L_Form : --GOOD-- ∀ (A : LFormula) (α : Finset String),
    L_closed_under_formula A α →                                      -- A formula in StarL is closed_under a set of variables if it was closed_under in L for the same set of variables.
    closed_under_formula (L_Form A) α

| cu_rel : --∀ (R : String) (ts : List Term) (α : Finset String),
    (∀ t, t ∈ ts → (match t with
                     | lcons lt => L_closed_under_term lt α
                     | _ => true))                                      -- TODO: não é sempre true, só se forem ground terms
    → closed_under_formula (rel R ts) α

| cu_eq : --∀ (t₁ t₂ : Term) (α : Finset String),
    (match t₁ with
     | lcons lt₁ => L_closed_under_term lt₁ α
     | _ => true) →
    (match t₂ with
     | lcons lt₂ => L_closed_under_term lt₂ α                           -- TODO: aqui não devia ser lt₁ com α e lt₂ com β? para depois ser a união?
     | _ => true) →
    closed_under_formula (t₁ =₁ t₂) α

| cu_mem : --∀ (t₁ t₂ : Term) (α : Finset String),
    (match t₁ with
     | lcons lt₁ => L_closed_under_term lt₁ α
     | _ => true) →
    (match t₂ with
     | lcons lt₂ => L_closed_under_term lt₂ α                           -- TODO: aqui não devia ser lt₁ com α e lt₂ com β? para depois ser a união?
     | _ => true) →
    closed_under_formula (t₁ ∈₁ t₂) α

| cu_not : --GOOD-- ∀ (A : Formula) (α : Finset String),
    closed_under_formula A α →                                            -- The negation of a formula is closed_under as long as the formula is closed_under
    closed_under_formula (¬₁ A) α

| cu_or : --GOOD-- ∀ (A B : Formula) (α β : Finset String),
    closed_under_formula A α →                                            -- The disjunction of two formulas is closed_under as long as both formulas are closed_under
    closed_under_formula B β →
    closed_under_formula (A ∨₁ B) (α ∪ β)

| cu_unbForall : --GOOD-- ∀ (x : String) (A : Formula) (α : Finset String),
    closed_under_formula A (α ∪ {x}) →                                    -- If a formula A is closed under a finite set α with the bound variable x, then ∀x A is closed under it as well
    closed_under_formula (V₁ x A) (α ∪ {x})

| cu_bForall : --∀ (x : String) (t : Term) (A : Formula) (α : Finset String),
    (match t with
     | Term.lcons lt => L_closed_under_term lt α
     | _ => true) →
    closed_under_formula A (α ∪ {x}) →
    closed_under_formula (bV₁ x t A) (α ∪ {x})                            -- TODO: aqui também com o _∪{x}
-/


/-
  x ∈ xs →                              -- sempre que A(x) precisamos das 2 primeiras linhas (se tivermos def de closed_under)
  closed_under_formula A xs →
-/








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

-- TO DO no: mudar def de substitution para que sejam Term.var em vez de String



-- ------------------------------------------
-- INTERPRETATION OF BOUNDED AXIOM OF CHOICE
-- ------------------------------------------

/-
lemma bAC_int_testinho
  (x y f a b : String) (A : Formula) (hAbase : isBase A) (y' g a' Φ f' : String):
  SH_int_comp2 (bAC_star_om x y f a b A) ([g]++[Φ],[x']++[f'],
    (((¬₁(b∀₁ [x] [var x'] (¬₁((b∀₁ [y] [var y'] (¬₁A)))))).subst ([y']⟹[var g·var x]))) ∨₁
      (((¬₁(b∀₁ [f] [var f'] (¬₁(b∀₁ [a] [var a'] (¬₁(b∀₁₁ b (var f·var a) (¬₁A))))))).subst
        ([a']⟹[var Φ·var f])))) :=
by
  -- LHS
  have notA := isBase.b_not hAbase
  have intNot1_L := SH_int_comp2.base notA
  have intUnbF1_L := @SH_int_comp2.unbForall (¬₁A) [] [] (¬₁A) [y] intNot1_L
  rw [[y].append_nil] at intUnbF1_L
  have intNot2_L := @SH_int_comp2.neg (∀₁₁ y (¬₁A)) [y] [] (¬₁A) [] [y'] intUnbF1_L
  rw [DoubleNeg] at intNot2_L
  have H1 := Subst_with_empty (b∃₁ [y] [y'].tt A) y
  rw [H1] at intNot2_L
  have intUnbF2_L := @SH_int_comp2.unbForall (¬₁(∀₁₁ y (¬₁A))) [] [y'] ((b∃₁ [y] [y'].tt A).subst ([]⟹[].tt⊙[y].tt)) [x] intNot2_L
  rw [[x].append_nil] at intUnbF2_L
  rw [H1] at intUnbF2_L
  have intNot3_L := @SH_int_comp2.neg (∀₁₁ x (¬₁(∀₁₁ y (¬₁A)))) [x] [y'] ((b∃₁ [y] [y'].tt A).subst ([]⟹[].tt⊙[y].tt)) [g] [x'] intUnbF2_L
  rw [H1] at intNot3_L
  -- RHS
  have exA := @bExists_base A b ((var f)·(var a)) hAbase
  have intB := SH_int_comp2.base exA
  have intUnbF1_R := @SH_int_comp2.unbForall (b∃₁₁ b ((var f)·(var a)) A) [] [] (b∃₁₁ b ((var f)·(var a)) A) [a] intB
  rw [[a].append_nil] at intUnbF1_R
  have intNot1_R := @SH_int_comp2.neg (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)) [a] [] (b∃₁₁ b ((var f)·(var a)) A) [] [a'] intUnbF1_R
  have H2 := Subst_with_empty (b∃₁ [a] [a'].tt (b∃₁₁ b (var f·var a) A).not) a
  rw [H2] at intNot1_R
  have intUnbF2_R := @SH_int_comp2.unbForall (¬₁(∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A))) [] [a'] ((b∃₁ [a] [a'].tt (¬₁(b∃₁₁ b (var f·var a) A))).subst ([]⟹[].tt⊙[a].tt)) [f] intNot1_R
  rw [[f].append_nil] at intUnbF2_R
  --have H3 := Subst_with_empty (b∃₁ [a] [a'].tt (b∃₁₁ b (var f·var a) A).not) a
  rw [H2] at intUnbF2_R
  have intNot2_R := @SH_int_comp2.neg (∀₁₁ f (¬₁(∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)))) [f] [a'] ((b∃₁ [a] [a'].tt (¬₁(b∃₁₁ b (var f·var a) A))).subst ([]⟹[].tt⊙[a].tt)) [Φ] [f'] intUnbF2_R
  rw [H2] at intNot2_R
  -- All together
  rw [bAC_star_om]
  have intForm := SH_int_comp2.disj intNot3_L intNot2_R
  simp
  rw [bExists, bExistsTuple, bExistsTuple, bExistsTuple, bExistsTuple] at intForm
  rw [DoubleNeg, DoubleNeg, DoubleNeg] at intForm
  exact intForm

lemma bAC_int2
  (x y f a b : String) (A : Formula) (hAbase : isBase A) (y' g a' Φ f' : String):
  SH_int_comp2 (bAC_star_om x y f a b A) ([g]++[Φ],[x']++[f'],
    (((¬₁(b∀₁ [x] [var x'] (¬₁((b∀₁ [y] [var y'] (¬₁A))).subst ([]⟹[])))).subst ([y']⟹[var g·var x]))) ∨₁
      (((¬₁(b∀₁ [f] [var f'] ((¬₁(b∀₁ [a] [var a'] (¬₁(b∀₁₁ b (var f·var a) (¬₁A))))).subst ([]⟹[])))).subst
        ([a']⟹[var Φ·var f])))) :=
by
  -- LHS
  have notA := isBase.b_not hAbase
  have intNot1_L := SH_int_comp2.base notA
  have intUnbF1_L := @SH_int_comp2.unbForall (¬₁A) [] [] (¬₁A) [y] intNot1_L
  rw [[y].append_nil] at intUnbF1_L
  have intNot2_L := @SH_int_comp2.neg (∀₁₁ y (¬₁A)) [y] [] (¬₁A) [] [y'] intUnbF1_L
  rw [DoubleNeg] at intNot2_L
  have intUnbF2_L := @SH_int_comp2.unbForall (¬₁(∀₁₁ y (¬₁A))) [] [y'] ((b∃₁ [y] [y'].tt A).subst ([]⟹[].tt⊙[y].tt)) [x] intNot2_L
  rw [[x].append_nil] at intUnbF2_L
  have intNot3_L := @SH_int_comp2.neg (∀₁₁ x (¬₁(∀₁₁ y (¬₁A)))) [x] [y'] ((b∃₁ [y] [y'].tt A).subst ([]⟹[].tt⊙[y].tt)) [g] [x'] intUnbF2_L
  -- RHS
  have exA := @bExists_base A b ((var f)·(var a)) hAbase
  have intB := SH_int_comp2.base exA
  have intUnbF1_R := @SH_int_comp2.unbForall (b∃₁₁ b ((var f)·(var a)) A) [] [] (b∃₁₁ b ((var f)·(var a)) A) [a] intB
  rw [[a].append_nil] at intUnbF1_R
  have intNot1_R := @SH_int_comp2.neg (∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)) [a] [] (b∃₁₁ b ((var f)·(var a)) A) [] [a'] intUnbF1_R
  have intUnbF2_R := @SH_int_comp2.unbForall (¬₁(∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A))) [] [a'] ((b∃₁ [a] [a'].tt (¬₁(b∃₁₁ b (var f·var a) A))).subst ([]⟹[].tt⊙[a].tt)) [f] intNot1_R
  rw [[f].append_nil] at intUnbF2_R
  have intNot2_R := @SH_int_comp2.neg (∀₁₁ f (¬₁(∀₁₁ a (b∃₁₁ b ((var f)·(var a)) A)))) [f] [a'] ((b∃₁ [a] [a'].tt (¬₁(b∃₁₁ b (var f·var a) A))).subst ([]⟹[].tt⊙[a].tt)) [Φ] [f'] intUnbF2_R
  -- All together
  rw [bAC_star_om]
  have intForm := SH_int_comp2.disj intNot3_L intNot2_R
  simp
  rw [bExists, bExistsTuple, bExistsTuple, bExistsTuple, bExistsTuple] at intForm
  rw [DoubleNeg, DoubleNeg, DoubleNeg] at intForm
  exact intForm
-/
