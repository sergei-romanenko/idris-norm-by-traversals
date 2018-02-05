module SemEnv


--
-- Semantics based on environments.
--

import Terms
import ExampleTerms

%access public export

%default total

mutual

  data Env : Type where
    Nil  : Env
    (::) : (Name , Clo) -> (r : Env) -> Env

  Clo : Type
  Clo = (Tm, Env)

lookup : (n : Name) -> (r : Env) -> Maybe Clo
lookup n [] = Nothing
lookup n ((m, c) :: r) =
  if n == m then Just c else lookup n r

remove : (n : Name) -> (r : Env) -> Env
remove n [] = []
remove n ((m, c) :: r) =
  if n == m then remove n r else (m, c) :: remove n r

fve : (r : Env) -> List Name
fve [] = []
fve ((n, (t', r')) :: r) =
  (fv t' `union` fve r') `union` fve r

rename : (x : Name) -> (t : Tm) -> (r : Env) -> (Name, Tm)
rename x t r =
  let ns = fve r in
  if elem x ns
  then (let y = fresh x (fv t `union` ns)
        in (y, substTm t x (Var y)))
  else (x , t)

cloToTm : (t : Tm) -> (r : Env) -> Tm
cloToTm t [] = t
cloToTm t  ((n, (t', r')) :: r) =
  cloToTm (substTm t n (cloToTm t' r')) r

%access private

covering
eval : (t : Tm) -> (r : Env) -> (w : Bool) -> Clo
eval (Var n) r w =
  case lookup n r of
    Nothing => (Var n, [])
    Just (t1, r1) => eval t1 r1 w
eval (Lam n t0) r True =
  let (n1, t1) = rename n t0 r
  in (Lam n1 t1, r)
eval (Lam n t0) r False =
  let (n1, t1) = rename n t0 r
      (t2, _) = eval t1 (remove n1 r) False
  in (Lam n1 t2, r)
eval (App f t) r w =
  let (f1, r1) = eval f r True in
  case f1 of
    (Lam n t0) => eval t0 ((n, (t, r)) :: r1) w
    _ => let (t1, _) = eval t r False in (App f1 t1, r)

covering
snf : (t : Tm) -> Tm
snf t =
  let (t1, r1) = eval t [] False
  in cloToTm t1 r1

-- Tests.

run : (t : Tm) -> String
run t = show $ assert_total $ snf t

-- Substitutions.

-- (\x y => x y y0) y = (\y1 => y y1 y0)
runSubst5 : run Subst5 = "(y1 => ((y y1) y0))"
runSubst5 = Refl

--
-- Church numerals.
--

runC1 : run C1 = "(s => (z => (s z)))"
runC1 = Refl

runC2 : run C2 = "(s => (z => (s (s z))))"
runC2 = Refl

runP22 : run P22 = "(s => (z => (s (s (s (s z))))))"
runP22 = Refl

runM22 : run M22 = "(s => (z => (s (s (s (s z))))))"
runM22 = Refl

--
-- Combinators
--

runSKK : run SKK = "(z => z)"
runSKK = Refl
