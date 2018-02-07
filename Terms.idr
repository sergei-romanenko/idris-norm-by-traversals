module Terms

--
-- Terms and substitutions.
--

%access public export

%default total

-- Variable names.

Name : Type
Name = String

-- Expressions.

data Tm : Type where
  Var : (n : Name) -> Tm
  Lam : (n : Name) -> (t0 : Tm) -> Tm
  App : (t1, t2 : Tm) -> Tm

implementation Show Tm where
  show (Var "") = "?"
  show (Var n) = n
  show (Lam n t0) = "(" ++ n ++ " => " ++ show t0 ++ ")"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"

-- Substitutions.

fv : (e : Tm) -> List Name
fv (Var n) = [n]
fv (Lam n e) = delete n (fv e)
fv (App e1 e2) = union (fv e1) (fv e2)

fresh' : (x : Name) -> (ns : List Name) -> (k : Nat) -> Name
fresh' x ns k =
  let x' = x ++ show k in
  if elem x' ns then assert_total $ fresh' x ns (S k) else x'

fresh : (x : Name) -> (ns : List Name) -> Name
fresh x ns =
  if elem x ns then fresh' x ns Z else x

substTm : (t : Tm) -> (n : Name) -> (u : Tm) -> Tm
substTm t n u =
  case t of
    (Var m) => if n == m then u else t
    (Lam m t0) =>
      if n == m then t
                else let m' = fresh m (fv t ++ fv u)
                         t0' = substTm t0 m (Var m')
                     in Lam m' (assert_total $ substTm t0' n u)
    (App t1 t2) => App (substTm t1 n u) (substTm t2 n u)

--
-- Tests.
--

%access private

run : (t : Tm) -> (n : Name) -> (u : Tm) -> String
run t n u = show $ substTm t n u

subst1 : run (Var "x") "y" (Var "z") = "x"
subst1 = Refl

subst2 : run (Var "x") "x" (Var "z") = "z"
subst2 = Refl

subst3 : run (Lam "x" (Var "x")) "x" (Var "z") = "(x => x)"
subst3 = Refl

subst4 : run (Lam "y" (Var "x")) "x" (Var "z") = "(y => z)"
subst4 = Refl

subst5 : run (Lam "y" (App (App (Var "x") (Var "y")) (Var "y0")))
             "x" (Var "y") =
             "(y1 => ((y y1) y0))"
subst5 = Refl
