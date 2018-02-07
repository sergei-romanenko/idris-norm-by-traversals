module Proofs.SemSubst

--
-- Some proofs related to `SemSubst`.
--

import Terms
import SemSubst
import ExampleTerms

%default total

--
-- Normal forms represented by data types.
--

-- Weak normal form.

mutual

  data WNf : Type where
    WLam : (x : Name) -> (t0 : Tm) -> WNf
    WNeu : (m : WNe) -> WNf

  data WNe : Type where
    WVar : (x : Name) -> WNe
    WApp : (m : WNe) -> (t : Tm) -> WNe

-- Embedding WNf into Tm.

mutual

  embWNf : (n : WNf) -> Tm
  embWNf (WLam x t0) = Lam x t0
  embWNf (WNeu m) = embWNe m

  embWNe : (m : WNe) -> Tm
  embWNe (WVar x) = Var x
  embWNe (WApp m t) = App (embWNe m) t

-- Strong normal form.

mutual

  data SNf : Type where
    SLam : (x : Name) -> (n0 : SNf) -> SNf
    SNeu : (m : SNe) -> SNf

  data SNe : Type where
    SVar : (x : Name) -> SNe
    SApp : (m : SNe) -> (n : SNf) -> SNe

-- Embedding SNf into Tm.

mutual

  embSNf : (n : SNf) -> Tm
  embSNf (SLam x n0) = Lam  x (embSNf n0)
  embSNf (SNeu m) = embSNe m

  embSNe : (m : SNe) -> Tm
  embSNe (SVar x) = Var x
  embSNe (SApp m n) = App (embSNe m) (embSNf n)

-- In order to proof something about a partial function,
-- we can turn it into a total one by adding a proof that
-- the function's argument belongs to its domain.
-- This technique is due to Bove & Capretta.

mutual

  partial
  pWnf : (t : Tm) -> WNf
  pWnf (Var x) = WNeu (WVar x)
  pWnf (Lam n t0) = WLam n t0
  pWnf (App t1 t2) = pWnfA (pWnf t1) t2

  partial
  pWnfA : (n1 : WNf) -> (t2 : Tm) -> WNf
  pWnfA (WLam x t0) t2 = pWnf (substTm t0 x t2)
  pWnfA (WNeu m) t2 = WNeu (WApp m t2)

mutual

  data DW : (t : Tm) -> Type where
    DWVar : DW (Var n)
    DWLam : DW (Lam n t0)
    DWApp : (d1 : DW t1) -> DWA (tWnf t1 d1) t2 -> DW (App t1 t2)

  data DWA : (n1 : WNf) -> (t2 : Tm) -> Type where
    DWALam : DW (substTm t0 x t2) -> DWA (WLam x t0) t2
    DWANeu : DWA (WNeu m) t2

  tWnf : (t : Tm) -> (d : DW t) -> WNf
  tWnf (Var x) DWVar = WNeu (WVar x)
  tWnf (Lam x t0) DWLam = WLam x t0
  tWnf (App t1 t2) (DWApp d1 d2) = tWnfA (tWnf t1 d1) t2 d2

  tWnfA : (n1 : WNf) -> (t2 : Tm) -> (d : DWA n1 t2) -> WNf
  tWnfA (WLam x t0) t2 (DWALam d) = tWnf (substTm t0 x t2) d
  tWnfA (WNeu m) t2 DWANeu = WNeu (WApp m t2)

mutual

  partial
  pSnf : (t : Tm) -> SNf
  pSnf (Var x) = SNeu (SVar x)
  pSnf (Lam x t0) = SLam x (pSnf t0)
  pSnf (App t1 t2) = pSnfA (pWnf t1) t2

  partial
  pSne : (m : WNe) -> SNe
  pSne (WVar x) = SVar x
  pSne (WApp m t) = SApp (pSne m) (pSnf t)

  partial
  pSnfA : (n1 : WNf) -> (t2 : Tm) -> SNf
  pSnfA (WLam x t0) t2 = pSnf (substTm t0 x t2)
  pSnfA (WNeu m) t2 = SNeu (SApp (pSne m) (pSnf t2))
