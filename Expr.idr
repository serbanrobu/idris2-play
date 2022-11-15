import Data.Fin

data Ctxt : Type

data Ty : Ctxt -> Type
    
data Term : (ctxt : Ctxt) -> Ty ctxt -> Type

data Var : (ctxt : Ctxt) -> Ty ctxt -> Type

data Sub : Ctxt -> Ctxt -> Type

(/) : Ty ctxt1 -> Sub ctxt1 ctxt2 -> Ty ctxt2

data Ctxt : Type where
    EmptyCtxt : Ctxt
    ExtCtxt : (ctxt : Ctxt) -> Ty ctxt -> Ctxt

-- uTy : Ty c

data Ty : Ctxt -> Type where
    UTy : Ty ctxt
    PiTy : (ty : Ty ctxt) -> Ty (ExtCtxt ctxt ty) -> Ty ctxt
    ElTy : Term ctxt Main.UTy -> Ty ctxt

-- uTy = Main.UTy

data Sub : Ctxt -> Ctxt -> Type where
    SubSub : Term ctxt ty -> Sub (ExtCtxt ctxt ty) ctxt
    WkSub : (ty : Ty ctxt) -> Sub ctxt (ExtCtxt ctxt ty)
    LiftSub : (sub : Sub ctxt1 ctxt2) -> (ty : Ty ctxt1) -> Sub (ExtCtxt ctxt1 ty) (ExtCtxt ctxt2 (ty / sub))
    IdSub : Sub ctxt ctxt
    ComposeSub : Sub ctxt1 ctxt2 -> Sub ctxt2 ctxt3 -> Sub ctxt1 ctxt3

data Term : (ctxt : Ctxt) -> Ty ctxt -> Type where
    VarTerm : Var ctxt ty -> Term ctxt ty
    LamTerm : Term (ExtCtxt ctxt ty1) ty2 -> Term ctxt (Main.PiTy ty1 ty2)
    AppTerm : Term ctxt (PiTy ty1 ty2) -> (term1 : Term ctxt ty1) -> Term ctxt (?a ty2 (SubSub term1))
    SubTerm : Term ctxt1 ty -> (sub : Sub ctxt1 ctxt2) -> Term ctxt2 (ty / sub)

Main.UTy / sub = UTy
Main.PiTy ty1 ty2 / sub = Main.PiTy (ty1 / sub) (ty2 / (Main.LiftSub sub ty1))
Main.ElTy term / sub = Main.ElTy (Main.SubTerm term sub)

data Var : (c : Ctxt) -> Ty c -> Type where