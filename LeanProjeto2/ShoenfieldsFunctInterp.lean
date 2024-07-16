--import LeanProjeto2.StarLang_old

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
    | isBase A => A
| V a E b A_ , V c E d B_ => V a V c E b E d (A_ ∨₁ B_)
    | {a} {b} A_ , c d B_ => {a c} {b d} (A_ ∨₁ B_)         USAR APPEND DAS LISTAS?
| SH_not
    | {a} {b} A_ =>                                         COMO CRIAR f a partir de b e a' a partir de a???
| SH_unb_forall
| SH_b_forall

-/


/-
def pi_app_transform2 : Term → Term
| (Π₁·q)·_ => q   -- Transform (Π₁·q)·_ to q
| t => t
-/
