module Proofs.Terms

--
-- Terms in normal form.
--

import Terms

%access public export

%default total

data NotLam : Tm -> Type where
  NLVar : NotLam (Var n)
  NLApp : NotLam (App t1 t2)

data IsNf : Tm -> Type where
  NfVar : IsNf (Var n)
  NfLam : IsNf t0 -> IsNf (Lam n t0)
  NfApp : NotLam t1 -> IsNf t1 -> IsNf t2 -> IsNf (App t1 t2)

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
