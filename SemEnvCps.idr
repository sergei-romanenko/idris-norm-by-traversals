module SemEnvCps

--
-- Semantics based on environments and CPS.
--

import Terms
import ExampleTerms
import SemEnv

%default total

covering
eval : (t : Tm) -> (r : Env) -> (w : Bool) -> (k : Clo -> Clo) -> Clo
eval (Var n) r w k =
  case lookup n r of
    Nothing => k (Var n, [])
    Just (t1, r1) => eval t1 r1 w k
eval (Lam n t0) r True k =
  let (n1, t1) = rename n t0 r
  in k (Lam n1 t1, r)
eval (Lam n t0) r False k =
  let (n1, t1) = rename n t0 r
  in eval t1 (remove n1 r) False (\(t2, _) => k (Lam n1 t2, r))
eval (App f t) r w k =
  eval f r True (\(f1, r1) =>
    case f1 of
      (Lam n t0) => eval t0 ((n, (t, r)) :: r1) w k
      _ => eval t r False (\(t1, _) => k (App f1 t1, r)))

covering
snf : (t : Tm) -> Tm
snf t =
  let (t1, r1) = eval t [] False id
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
