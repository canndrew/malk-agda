open import Agda.Builtin.Equality public

open import Eqs



data Ctx : Set

data Level : Set

data Form : Ctx -> Level -> Set

data Rype : Ctx -> Level -> Set

data In : (c : Ctx) -> {cv : Ctx} -> {lv : Level} -> (Rype cv lv) -> Set

data Elim : (c : Ctx) -> (l : Level) -> Rype c l -> Set

data Term : (c : Ctx) -> (l : Level) -> Rype c l -> Set


substituteCtx : (cr : Ctx)
             -> {cv : Ctx}
             -> {lv : Level}
             -> {rv : Rype cv lv}
             -> (tv : Term cv lv rv)
             -> (i : In cr rv)
             -> Ctx
substituteForm : {cf : Ctx}
              -> {lf : Level}
              -> Form cf lf
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Rype cv lv}
              -> (tv : Term cv lv rv)
              -> (i : In cf rv)
              -> Form (substituteCtx cf tv i) lf
substituteRype : {cr : Ctx}
              -> {lr : Level}
              -> Rype cr lr
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Rype cv lv}
              -> (tv : Term cv lv rv)
              -> (i : In cr rv)
              -> Rype (substituteCtx cr tv i) lr
substituteTerm : {ct : Ctx}
              -> {lt : Level}
              -> {rt : Rype ct lt}
              -> Term ct lt rt
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Rype cv lv}
              -> (tv : Term cv lv rv)
              -> (i : In ct rv)
              -> Term (substituteCtx ct tv i) lt (substituteRype rt tv i)
substituteElim : {ce : Ctx}
              -> {le : Level}
              -> {re : Rype ce le}
              -> Elim ce le re
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Rype cv lv}
              -> (tv : Term cv lv rv)
              -> (i : In ce rv)
              -> Term (substituteCtx ce tv i) le (substituteRype re tv i)

data Ctx where
    CNil : Ctx
    CCons : (c : Ctx) -> (l : Level) -> Rype c l -> Ctx

data Level where
    LZero : Level
    LSucc : Level -> Level

lmax : Level -> Level -> Level
lmax LZero b = LSucc b
lmax (LSucc a) LZero = LSucc a
lmax (LSucc a) (LSucc b) = LSucc (lmax a b)

data Form where
    FRype : {c : Ctx}
         -> (l : Level)
         -> Form c (LSucc l)
    FNever : {c : Ctx}
          -> {l : Level}
          -> Form c l
    FUnit : {c : Ctx}
         -> {l : Level}
         -> Form c l
    FFunc : {c : Ctx}
         -> {la : Level}
         -> (ra : Rype c la)
         -> {lb : Level}
         -> Rype (CCons c la ra) lb
         -> Form c (lmax la lb)
    FPair : {c : Ctx}
         -> {lh : Level}
         -> (rh : Rype c lh)
         -> {lt : Level}
         -> Rype (CCons c lh rh) lt
         -> Form c (lmax lh lt)

data Rype where
    RWeaken : {c : Ctx}
           -> {lr : Level}
           -> Rype c lr
           -> {ld : Level}
           -> {rd : Rype c ld}
           -> Rype (CCons c ld rd) lr

    RForm : {c : Ctx}
         -> {l : Level}
         -> Form c l
         -> Rype c l

    RElim : {c : Ctx}
         -> {l : Level}
         -> Elim c (LSucc l) (RForm (FRype l))
         -> Rype c l

data In where
    ITop : {c : Ctx}
        -> {lv : Level}
        -> {rv : Rype c lv}
        -> In (CCons c lv rv) rv
    IPop : {c : Ctx}
        -> {ld : Level}
        -> {rd : Rype c ld}
        -> {cv : Ctx}
        -> {lv : Level}
        -> {rv : Rype cv lv}
        -> In c rv
        -> In (CCons c ld rd) rv

substituteCtx (CCons cr lv rv) tv ITop = cr
substituteCtx (CCons cr ld rd) tv (IPop i) = CCons (substituteCtx cr tv i) ld (substituteRype rd tv i)

broadenPost : {c : Ctx}
           -> {cx : Ctx}
           -> {lx : Level}
           -> {rx : Rype cx lx}
           -> {tx : Term cx lx rx}
           -> (ix : In c rx)
           -> {cy : Ctx}
           -> {ly : Level}
           -> {ry : Rype cy ly}
           -> (iy : In cx ry)
           -> In (substituteCtx c tx ix) ry
broadenPost ITop iy = iy
broadenPost (IPop ix) iy = IPop (broadenPost ix iy)

broadenPre : {c : Ctx}
          -> {cx : Ctx}
          -> {lx : Level}
          -> {rx : Rype cx lx}
          -> {tx : Term cx lx rx}
          -> (ix : In c rx)
          -> {cy : Ctx}
          -> {ly : Level}
          -> {ry : Rype cy ly}
          -> (iy : In cx ry)
          -> In c ry
broadenPre ITop iy = IPop iy
broadenPre (IPop ix) iy = IPop (broadenPre ix iy)

broadenStill : {c : Ctx}
            -> {cx : Ctx}
            -> {lx : Level}
            -> {rx : Rype cx lx}
            -> {tx : Term cx lx rx}
            -> (ix : In c rx)
            -> {cy : Ctx}
            -> {ly : Level}
            -> {ry : Rype cy ly}
            -> {ty : Term cy ly ry}
            -> (iy : In cx ry)
            -> In (substituteCtx c ty (broadenPre ix iy)) (substituteRype rx ty iy)
broadenStill ITop iy = ITop
broadenStill (IPop ix) iy = IPop (broadenStill ix iy)

reorderCtx : {c : Ctx}
          -> {cx : Ctx}
          -> {lx : Level}
          -> {rx : Rype cx lx}
          -> {tx : Term cx lx rx}
          -> (ix : In c rx)
          -> {cy : Ctx}
          -> {ly : Level}
          -> {ry : Rype cy ly}
          -> {ty : Term cy ly ry}
          -> (iy : In cx ry)
          -> (substituteCtx (substituteCtx c tx ix) ty (broadenPost ix iy)) ≡
             (substituteCtx (substituteCtx c ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy))

reorderRype : {c : Ctx}
           -> {l : Level}
           -> {r : Rype c l}
           -> {cx : Ctx}
           -> {lx : Level}
           -> {rx : Rype cx lx}
           -> {tx : Term cx lx rx}
           -> (ix : In c rx)
           -> {cy : Ctx}
           -> {ly : Level}
           -> {ry : Rype cy ly}
           -> {ty : Term cy ly ry}
           -> (iy : In cx ry)
           -> (substituteRype (substituteRype r tx ix) ty (broadenPost ix iy)) ===
              (substituteRype (substituteRype r ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy))

reorderForm : {c : Ctx}
           -> {l : Level}
           -> {f : Form c l}
           -> {cx : Ctx}
           -> {lx : Level}
           -> {rx : Rype cx lx}
           -> {tx : Term cx lx rx}
           -> (ix : In c rx)
           -> {cy : Ctx}
           -> {ly : Level}
           -> {ry : Rype cy ly}
           -> {ty : Term cy ly ry}
           -> (iy : In cx ry)
           -> (substituteForm (substituteForm f tx ix) ty (broadenPost ix iy)) ===
              (substituteForm (substituteForm f ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy))

reorderElim : {c : Ctx}
           -> {l : Level}
           -> {r : Rype c l}
           -> {e : Elim c l r}
           -> {cx : Ctx}
           -> {lx : Level}
           -> {rx : Rype cx lx}
           -> {tx : Term cx lx rx}
           -> (ix : In c rx)
           -> {cy : Ctx}
           -> {ly : Level}
           -> {ry : Rype cy ly}
           -> {ty : Term cy ly ry}
           -> (iy : In cx ry)
           -> (substituteTerm (substituteElim e tx ix) ty (broadenPost ix iy)) ===
              (substituteTerm (substituteElim e ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy))

reorderTerm : {c : Ctx}
           -> {l : Level}
           -> {r : Rype c l}
           -> {t : Term c l r}
           -> {cx : Ctx}
           -> {lx : Level}
           -> {rx : Rype cx lx}
           -> {tx : Term cx lx rx}
           -> (ix : In c rx)
           -> {cy : Ctx}
           -> {ly : Level}
           -> {ry : Rype cy ly}
           -> {ty : Term cy ly ry}
           -> (iy : In cx ry)
           -> (substituteTerm (substituteTerm t tx ix) ty (broadenPost ix iy)) ===
              (substituteTerm (substituteTerm t ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy))


reorderCtx ITop iy = refl
reorderCtx {CCons c ld rd} {cx} {lx} {rx} {tx} (IPop ix) {cy} {ly} {ry} {ty} iy =
    let scXY : Ctx
        scXY = (substituteCtx (substituteCtx c tx ix) ty (broadenPost ix iy))
    in
    let scYX : Ctx
        scYX = (substituteCtx (substituteCtx c ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy))
    in
    let floo : scXY ≡ scYX
        floo = reorderCtx ix iy
    in
    let flooz : scXY === scYX
        flooz = homoToHetero floo
    in
    let srdXY : Rype scXY ld
        srdXY = substituteRype (substituteRype rd tx ix) ty (broadenPost ix iy)
    in
    let srdYX : Rype scYX ld
        srdYX = substituteRype (substituteRype rd ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy)
    in
    let resrd : srdXY === srdYX
        resrd = reorderRype ix iy
    in
    let bong : (CCons scXY ld srdXY) === (CCons scYX ld srdYX)
        bong = cong3Het CCons flooz refl resrd
    in
    heteroToHomo bong


intoRype : {c : Ctx}
        -> {l : Level}
        -> Term c (LSucc l) (RForm (FRype l)) -> Rype c l


substituteForm (FRype l) tv i = FRype l
substituteForm FNever tv i = FNever
substituteForm FUnit tv i = FUnit
substituteForm (FFunc ra rb) tv i = FFunc (substituteRype ra tv i) (substituteRype rb tv (IPop i))
substituteForm (FPair rh rt) tv i = FPair (substituteRype rh tv i) (substituteRype rt tv (IPop i))

substituteRype (RWeaken rr) tv ITop = rr
substituteRype (RWeaken rr) tv (IPop i) = RWeaken (substituteRype rr tv i)
substituteRype (RForm f) tv i = RForm (substituteForm f tv i)
substituteRype (RElim e) tv i = intoRype (substituteElim e tv i)


reorderForm {_} {_} {FRype l} ITop iy = refl
reorderForm {_} {_} {FRype l} (IPop ix) iy = refl
reorderForm {c} {l} {FNever} ITop iy = refl
reorderForm {c} {l} {FNever} (IPop ix) iy = refl
reorderForm {c} {l} {FUnit} ITop iy = refl
reorderForm {c} {l} {FUnit} (IPop ix) iy = refl
reorderForm {c} {_} {FFunc ra rb} ITop iy =
    cong2ImplHet (reorderForm ITop iy) (reorderForm (IPop ITop) iy)
reorderForm {c} {_} {FFunc ra rb} (IPop ix) iy =
    cong2ImplHet (reorderForm (IPop ix) iy) (reorderForm (IPop (IPop ix)) iy)
reorderForm {c} {_} {FPair rh rt} ITop iy =
    cong2ImplHet (reorderForm ITop iy) (reorderForm (IPop ITop) iy)
reorderForm {c} {_} {FPair rh rt} (IPop ix) iy =
    cong2ImplHet (reorderForm (IPop ix) iy) (reorderForm (IPop (IPop ix)) iy)

reorderRype {_} {_} {RWeaken r} ITop iy = refl
reorderRype {_} {_} {RWeaken r} (IPop ix) iy = refl
reorderRype {_} {_} {RForm x} ITop iy =
    cong1ImplHet (reorderForm ITop iy)
reorderRype {_} {_} {RForm x} (IPop ix) iy =
    cong1ImplHet (reorderForm (IPop ix) iy)
reorderRype {_} {l} {RElim x} ITop iy =
    cong1ImplHet (reorderElim ITop iy)
reorderRype {_} {l} {RElim x} (IPop ix) iy =
    cong1ImplHet (reorderElim (IPop ix) iy)
    





neverElim : {c : Ctx}
         -> {l : Level}
         -> Term c l (RForm FNever)
         -> Elim c l (RForm FNever)

tapp : {c : Ctx}
    -> {la : Level}
    -> {ra : Rype c la}
    -> {lb : Level}
    -> {rb : Rype (CCons c la ra) lb}
    -> Term c (lmax la lb) (RForm (FFunc ra rb))
    -> (ta : Term c la ra)
    -> Term c lb (substituteRype rb ta ITop)

{-
tbust : {c : Ctx}
     -> {lh : Level}
     -> {rh : Rype c lh}
     -> {lt : Level}
     -> {rt : Rype (CCons c lh rh) lt}
     -> (tp : Term c (lmax lh lt) (RForm (FPair rh rt)))
     -> {lb : Level}
     -> {rb : Rype (CCons c (lmax lh lt) (RForm (FPair rh rt))) lb}
     -> (tr : Term (CCons c (lmax lh lt) (RForm (FPair rh rt))) lb rb)
     -> Term c lb (substituteRype rb tp ITop)
-}

data Term where
    TWeaken : {c : Ctx}
           -> {lt : Level}
           -> {rt : Rype c lt}
           -> Term c lt rt
           -> {ld : Level}
           -> {rd : Rype c ld}
           -> Term (CCons c ld rd) lt (RWeaken rt)

    TUnit : {c : Ctx}
         -> Term c LZero (RForm FUnit)
    TFunc : {c : Ctx}
         -> {la : Level}
         -> {ra : Rype c la}
         -> {lb : Level}
         -> {rb : Rype (CCons c la ra) lb}
         -> Term (CCons c la ra) lb rb
         -> Term c (lmax la lb) (RForm (FFunc ra rb))
    TPair : {c : Ctx}
         -> {lh : Level}
         -> {rh : Rype c lh}
         -> {lt : Level}
         -> {rt : Rype (CCons c lh rh) lt}
         -> (th : Term c lh rh)
         -> (tt : Term c lt (substituteRype rt th ITop))
         -> Term c (lmax lh lt) (RForm (FPair rh rt))

    TEmbedForm : {c : Ctx}
              -> {l : Level}
              -> Form c l
              -> Term c (LSucc l) (RForm (FRype l))

    TEmbedElim : {c : Ctx}
              -> {l : Level}
              -> {r : Rype c l}
              -> Elim c l r
              -> Term c l r

{-
rypeToTerm : {c : Ctx}
          -> {l : Level}
          -> {r : Rype c l}
          -> Term c (LSucc l) (RForm (FRype l))
rypeToTerm (RWeaken r) = 
rypeToTerm (RForm f) = TEmbedForm f
-}


data Elim where
    EVar : {c : Ctx}
        -> {lv : Level}
        -> {rv : Rype c lv}
        -> Elim (CCons c lv rv) lv (RWeaken rv)

    EAbort : {c : Ctx}
          -> Elim c LZero (RForm FNever)
          -> {lr : Level}
          -> (r : Rype c lr)
          -> Elim c lr r

    EFunc : {c : Ctx}
         -> {la : Level}
         -> {ra : Rype c la}
         -> {lb : Level}
         -> {rb : Rype (CCons c la ra) lb}
         -> (ef : Elim c (lmax la lb) (RForm (FFunc ra rb)))
         -> (ta : Term c la ra)
         -> Elim c lb (substituteRype rb ta ITop)

    {-
    EPair : {c : Ctx}
         -> {lh : Level}
         -> {rh : Rype c lh}
         -> {lt : Level}
         -> {rt : Rype (CCons c lh rh) lt}
         -> (ep : Elim c (lmax lh lt) (RForm (FPair rh rt)))
         -> {lb : Level}
         -> {rb : Rype (CCons (CCons c lh rh) lt rt) lb}
         -> (tb : Term (CCons (CCons c lh rh) lt rt) lb rb)
         -> Elim c lb (RElim (EPair ep (rypeToTerm rb)))
    -}



neverElim (TEmbedElim e) = e

tapp (TFunc rb) ta = substituteTerm rb ta ITop
tapp (TEmbedElim ef) ta = TEmbedElim (EFunc ef ta)

--tbust (TPair th tt) tb = substituteTerm 

intoRype (TEmbedForm f) = RForm f
intoRype (TEmbedElim e) = RElim e

substituteElim EVar tv ITop = tv
substituteElim EVar tv (IPop i) = TEmbedElim EVar
substituteElim (EAbort en rb) tv i =
    let sen = neverElim (substituteElim en tv i) in
    let srb = substituteRype rb tv i in
    TEmbedElim (EAbort sen srb)
substituteElim (EFunc ef ta) tv i =
    let stf = substituteElim ef tv i in
    let sta = substituteTerm ta tv i in
    let got = tapp stf sta in
    let same0 = reorderRype ITop i in
    let same1 = cong1ImplHet same0 in
    let same2 = heteroToHomo same1 in
    transport same2 got
{-
substituteElim (EPair ep tr) tv i =
    let stp = substituteElim ep tv i in
    let str = substituteTerm tr tv (IPop i) in
    let got = tbust stp str
    got
-}



substituteTerm (TWeaken t) tv ITop = t
substituteTerm (TWeaken t) tv (IPop i) = TWeaken (substituteTerm t tv i)
substituteTerm TUnit tv i = TUnit
substituteTerm (TFunc tb) tv i = 
    let stb = substituteTerm tb tv (IPop i) in
    TFunc stb
substituteTerm (TPair th tt) tv i =
    let sth = substituteTerm th tv i in
    let stt = substituteTerm tt tv i in
    let same0 = reorderRype ITop i in
    let same1 = cong1ImplHet same0 in
    let same2 = heteroToHomo same1 in
    TPair sth (transport same2 stt)
substituteTerm (TEmbedForm f) tv i = TEmbedForm (substituteForm f tv i)
substituteTerm (TEmbedElim e) tv i = substituteElim e tv i

reorderElim {_} {_} {_} {EVar} ITop iy = refl
reorderElim {_} {_} {_} {EVar} (IPop ix) iy = refl
reorderElim {_} {_} {_} {EAbort e r} ITop iy =
    cong2ImplHet (cong1Het neverElim (reorderElim ITop iy)) (reorderRype ITop iy)
reorderElim {_} {_} {_} {EAbort e r} (IPop ix) iy =
    cong2ImplHet (cong1Het neverElim (reorderElim (IPop ix) iy)) (reorderRype (IPop ix) iy)
reorderElim {_} {_} {_} {EFunc e ta} ITop iy =
    cong2ImplHet (reorderElim ITop iy) (reorderTerm ITop iy)
reorderElim {_} {_} {_} {EFunc e ta} (IPop ix) iy = ?
    cong2ImplHet (reorderElim (IPop ix) iy) (reorderTerm (IPop ix) iy)

reorderTerm {_} {_} {_} {TWeaken t} ITop iy = refl
reorderTerm {_} {_} {_} {TWeaken t} (IPop ix) iy = refl
reorderTerm {_} {_} {_} {TUnit} ITop iy = refl
reorderTerm {_} {_} {_} {TUnit} (IPop ix) iy = refl
reorderTerm {_} {_} {_} {TFunc tb} ITop iy = 
    cong1ImplHet (reorderTerm ITop iy)
reorderTerm {_} {_} {_} {TFunc tb} (IPop ix) iy =
    cong1ImplHet (reorderTerm (IPop ix) iy)
reorderTerm {_} {_} {_} {TPair th tt} ITop iy =
    cong2ImplHet (reorderTerm ITop iy) (reorderTerm ITop iy)
reorderTerm {_} {_} {_} {TPair tt th} (IPop ix) iy =
    cong2ImplHet (reorderTerm (IPop ix) iy) (reorderTerm (IPop ix) iy)
reorderTerm {_} {_} {_} {TEmbedForm f} ITop iy =
    cong1ImplHet (reorderForm ITop iy)
reorderTerm {_} {_} {_} {TEmbedForm f} (IPop ix) iy =
    cong1ImplHet (reorderForm (IPop ix) iy)
reorderTerm {_} {_} {_} {TEmbedElim e} ITop iy =
    reorderElim ITop iy
reorderTerm {_} {_} {_} {TEmbedElim e} (IPop ix) iy =
    reorderElim (IPop ix) iy

