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

data NotLam : Tm -> Type where
  NLVar : NotLam (Var n)
  NLApp : NotLam (App t1 t2)

data IsNf : Tm -> Type where
  NfVar : IsNf (Var n)
  NfLam : IsNf t0 -> IsNf (Lam n t0)
  NfApp : NotLam t1 -> IsNf t1 -> IsNf t2 -> IsNf (App t1 t2)

{-
data IsLam : Tm -> Type where
  OkLam : IsLam (Lam n t0)

implementation Uninhabited (IsLam (Var x)) where
  uninhabited OkLam impossible

implementation Uninhabited (IsLam (App t1 t2)) where
  uninhabited OkLam impossible

decLam : (t : Tm) -> Dec (IsLam t)
decLam (Var n) = No absurd
decLam (Lam n t0) = Yes OkLam
decLam (App t1 t2) = No absurd
-}

implementation Uninhabited (NotLam (Lam n t0)) where
  uninhabited NLVar impossible
  uninhabited NLApp impossible

decNotLam : (t : Tm) -> Dec (NotLam t)
decNotLam (Var n) = Yes NLVar
decNotLam (Lam n t0) = No absurd
decNotLam (App t1 t2) = Yes NLApp

decNf : (t : Tm) -> Dec (IsNf t)
decNf (Var n) = Yes NfVar
decNf (Lam n t0) with (decNf t0)
  decNf (Lam n t0) | (Yes nf0) = Yes (NfLam nf0)
  decNf (Lam n t0) | (No nnf0) = No (\(NfLam nf0) => nnf0 nf0)
decNf (App t1 t2) with (decNotLam t1, decNf t1, decNf t2)
  | (Yes nl1, Yes nf1, Yes nf2) = Yes (NfApp nl1 nf1 nf2)
  | (No nnl1, _,       _      ) = No (\(NfApp nl1 _ _) => nnl1 nl1)
  | (_,       No nnf1, _      ) = No (\(NfApp _ nf1 _) => nnf1 nf1)
  | (_,       _,       No nnf2) = No (\(NfApp _ _ nf2) => nnf2 nf2)


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

%access private

run : (t : Tm) -> (n : Name) -> (u : Tm) -> String
run t n u = show $ substTm t n u

Subst1 : run (Var "x") "y" (Var "z") = "x"
Subst1 = Refl

Subst2 : run (Var "x") "x" (Var "z") = "z"
Subst2 = Refl

Subst3 : run (Lam "x" (Var "x")) "x" (Var "z") = "(x => x)"
Subst3 = Refl

Subst4 : run (Lam "y" (Var "x")) "x" (Var "z") = "(y => z)"
Subst4 = Refl

Subst5 : run (Lam "y" (App (App (Var "x") (Var "y")) (Var "y0")))
             "x" (Var "y") =
             "(y1 => ((y y1) y0))"
Subst5 = Refl
