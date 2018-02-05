module SemHistRenaming

--
-- Semantics based on histories and renaming bound variables.
-- Note that this version is TERRIBLY inefficient, because it
-- repeatedly recomputes the sets of variables free in the histories.
--

import Terms
import ExampleTerms

%default total

-- Histories.

mutual

  Hist : Type
  Hist = List Item

  data Item : Type where
    HI : (t : Tm) -> (w : Bool) -> (b, c : Hist) -> Item

implementation Show Item where
  show (HI t w b c) = show t

-- Renaming variables.

fvh : (h : Hist) -> List Name
fvh [] = []
fvh ((HI t w b c) :: h) =
  fv t ++ (fvh b ++ (fvh c ++ fvh h))

-- `(Lam x t)` is supposed to appear in `h`.

rename : (x : Name) -> (t : Tm) -> (h : Hist) -> (Name, Tm)
rename x t h =
  let ns = fvh h in
  if elem x ns
  then (let y = fresh x ns
        in (y, substTm t x (Var y)))
  else (x , t)

-- Evaluation.

partial
lookup : (n : Name) -> (b : Hist) -> (Tm, Hist)
lookup n [] = (Var "" , [])
lookup n (hi :: _) = case hi of
  HI (Lam m _) True b c => case n == m of
    True => case c of
      HI (App _ t2) _ b' _ :: _ => (t2, b')
    False => lookup n b
  HI (Lam m _) False b _ => case n == m of
    True => (Var "", [])
    False => lookup n b
  HI _ _ b _ => lookup n b

mutual

  partial
  eval : (h : Hist) -> Hist
  eval [] = [HI (Var "") False [] []] -- Remove?
  eval h = case h of
    HI t w b c :: h' => case t of
      (Var n) => case lookup n b of
        (Var "", _) => apk t c h
        (t', b') => eval (HI t' w b' c :: h)
      (Lam n t0) =>
        let (n1, t1) = rename n t0 h
            h1 = HI (Lam n1 t1) w b c :: h'
        in
        case w of
          True => apk (Lam n1 t1) c h1
          False => eval (HI t1 False h1 c :: h1)
      (App t1 t2) =>
        eval (HI t1 True b h :: h)

  partial
  apk : (t : Tm) -> (c, h : Hist) -> Hist
  apk t [] h = h
  apk t (HI (App t1 t2) w b c :: _) h = case t of
    (Lam n t0) => eval (HI t0 w h c :: h)
    _ => eval (HI t2 False b c :: h)

partial
evalTm : (t : Tm) -> Hist
evalTm t = eval [HI t False [] []]

-- Cleaning the history.

partial
clean' : (h : Hist) -> (i : Nat) -> List Nat
clean' [] i = []
clean' ((HI (Var n) w b c) :: h) i =
  case lookup n b of
    (Var "", []) => clean' h (S i)
    (_, _) => i :: clean' h (S i)
clean' ((HI (Lam n t0) True b []) :: h) i =
  clean' h (S i)
clean' ((HI (Lam n t0) True b c) :: h) i =
  i :: length c :: clean' h (S i)
clean' ((HI (Lam n t0) False b c) :: h) i =
  clean' h (S i)
clean' ((HI (App t1 t2) w b c) :: h) i =
  clean' h (S i)
--clean' ((HI t w b c) :: h) i =
--  clean' h (S i)

partial
clean : Hist -> List Item
clean h = map snd $ filter (\(i, _) => not (elem i (clean' h 1)))
                           (zip [1 .. S (length h)] h)


-- Building the normalized term from the cleaned history.

build' : (h : Hist) -> (ts : List Tm) -> Tm
build' [] (t :: ts) = t
build' (HI (Var n) w b c :: h) ts =
  build' h (Var n :: ts)
build' (HI (Lam n _) w b c :: h) (t :: ts) =
  build' h (Lam n t :: ts)
build' (HI (App _ _) w b c :: h) (t1 :: t2 :: ts) =
  build' h (App t1 t2 :: ts)
build' h ts =
  Var ("?build' " ++ show h ++ " " ++ show ts)

build : (h : Hist) -> Tm
build h = build' (reverse h) []

-- Getting the strong normal form.

partial
snf : (t : Tm) -> Tm
snf = build . clean . reverse . evalTm

--
-- Tests.
--

run : (t : Tm) -> String
run t =
  show $ build $ assert_total $ clean $ reverse $ assert_total $ evalTm t

tst : (t : Tm) -> (expected : String) -> String
tst t expected =
  show t ++ " ~~~> " ++ produced ++ "  " ++
    (if expected == produced then "OK" else "Wrong! Expected: " ++ expected)
  where produced : String
        produced = run t

-- Substitutions.

tstSubst5 : String
tstSubst5 = tst Subst5 "(y1 => ((y y1) y0))"


--
-- Church numerals.
--

tstC1 : String
tstC1 = tst C1 "(#1 => (#2 => (#1 #2)))"

tstC2 : String
tstC2 = tst C2 "(s => (z => (s z)))"

tstP22 : String
tstP22 = tst P22 "(s => (z => (s (s (s (s z))))))"

tstM22 : String
tstM22 = tst M22 "(s => (z => (s (s (s (s z))))))"

--
-- Combinators
--

tstSKK : String
tstSKK = tst SKK "(z => z)"
