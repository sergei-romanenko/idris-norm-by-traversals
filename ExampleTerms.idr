module ExampleTerms

--
-- Example terms.
--

import Terms

%access public export

%default total

-- Substitutions.

-- (\y => x) z = x
Subst1 : Tm
Subst1 = App (Lam "y" (Var "x")) (Var "z")

-- (\x => x) z = z
Subst2 : Tm
Subst2 = App (Lam "x" (Var "x")) (Var "z")

-- (\x x => x) z = (\x => x)
Subst3 : Tm
Subst3 = App (Lam "x" (Lam "x" (Var "x"))) (Var "z")

-- (\x y => x) z = (\y => z)
Subst4 : Tm
Subst4 = App (Lam "x" (Lam "y" (Var "x"))) (Var "z")

-- (\x y => x y y0) y = (\y1 => y y1 y0)
Subst5 : Tm
Subst5 = App (Lam "x" (Lam "y"
                  (App (App (Var "x") (Var "y")) (Var "y0"))))
             (Var "y")

-- Church numerals.

-- zero = \s z => z
Zero : Tm
Zero = Lam "s" (Lam "z" (Var "z"))

-- one = \s z => s z
One : Tm
One = Lam "s" (Lam "z" (App (Var "s") (Var "z")))

-- two = \s z => s (s z)
Two : Tm
Two = Lam "s" (Lam "z" (App (Var "s") (App (Var "s") (Var "z"))))

-- two = \s z => s (s (s z))
Three : Tm
Three = Lam "s" (Lam "z"
            (App (Var "s") (App (Var "s") (App (Var "s") (Var "z")))))

-- suc = \k s z => s (k s z)
Suc : Tm
Suc = Lam "k" (Lam "s" (Lam "z"
  (App (Var "s") (App (App (Var "k") (Var "s")) (Var "z")))))

-- plus = \m n s z => (m s) ((n s) z)
Plus : Tm
Plus = Lam "m" (Lam "n" (Lam "s" (Lam "z"
  (App (App (Var "m") (Var "s"))
         (App (App (Var "n") (Var "s")) (Var "z"))))))

-- mult = \m n s z => m (n s) z
Mult : Tm
Mult = Lam "m" (Lam "n" (Lam "s" (Lam "z"
  (App (App (Var "m") (App (Var "n") (Var "s"))) (Var "z")))))

TWO : Tm
TWO = App (Var "S") (App (Var "S") (Var "Z"))

C1 : Tm
C1 = App Suc Zero

C2 : Tm
C2 = App Suc C1

P22 : Tm
P22 = App (App Plus Two) Two

M22 : Tm
M22 = App (App Mult Two) Two

--
-- Combinators
--

-- x => x
I : Tm
I = Lam "x" (Var "x")

-- \x y => x
K : Tm
K = Lam "x" (Lam "y" (Var "x"))

-- \x y z => (x z) (y z)
S : Tm
S = Lam "x" (Lam "y" (Lam "z"
  (App (App (Var "x") (Var "z")) (App (Var "y") (Var "z")))))

-- S K K
SKK : Tm
SKK = App (App S K) K

-- \x => x x
Delta : Tm
Delta = Lam "x" (App (Var "x") (Var "x"))

-- (x => x x) (\x => x x)
Omega : Tm
Omega = (App Delta Delta)

-- f => (x => (f x) x) (x => (f x) x)

Y : Tm
Y = Lam "f" (App (Lam "x" (App (App (Var "f") (Var "x")) (Var "x")))
                 (Lam "x" (App (App (Var "f") (Var "x")) (Var "x"))))
