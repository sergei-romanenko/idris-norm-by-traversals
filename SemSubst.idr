module SemSubst

--
-- Semantics based on substitutions.
--

import Terms
import ExampleTerms

%default total

-- Normalization of terms.

covering
wnf : (t : Tm) -> Tm
wnf (Var n) = Var n
wnf (Lam n t0) = Lam n t0
wnf (App t1 t2) =
  case wnf t1 of
    Lam n t0 => wnf (substTm t0 n t2)
    t => App t t2

covering
snf : (t : Tm) -> Tm
snf (Var n) = Var n
snf (Lam n t0) = Lam n (snf t0)
snf (App t1 t2) =
  case wnf t1 of
    Lam n t0 => snf (substTm t0 n t2)
    t => App (snf t) (snf t2)

-- Tests.

run : (t : Tm) -> String
run t = show $ assert_total $ snf t

--
-- Substitutions.
--

-- (\x y => x y y0) y = (\y1 => y y1 y0)
tstSubst5 : run Subst5 = "(y1 => ((y y1) y0))"
tstSubst5 = Refl
--

--
-- Church numerals.
--

tstC1 : run C1 = "(s => (z => (s z)))"
tstC1 = Refl

tstC2 : run C2 = "(s => (z => (s (s z))))"
tstC2 = Refl

tstP22 : run P22 = "(s => (z => (s (s (s (s z))))))"
tstP22 = Refl

tstM22 : run M22 = "(s => (z => (s (s (s (s z))))))"
tstM22 = Refl

--
-- Combinators
--

tstSKK : run SKK = "(z => z)"
tstSKK = Refl
