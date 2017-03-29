open import Agda.Builtin.Equality public

open import Eqs

-- Problem: weakening rules are broken.
-- Solution?: change weakening from a kind of syntax to just a function. Figure
-- out linearity later, probably by changing the way contexts are represented
-- so that we can say (eg.) TUnit is valid under any linear-free context.



-- A work-in-progress implementation of type theory in Agda. This is intended
-- to be a starting point for playing around with type-theoretic ideas and
-- verifying that they're sound.
-- PLAN:
--  * Finish implementing sigma types
--  * Add recursive types (with sizes) and identity types
--  * Add support for linear-dependent types a.la. Connor McBride's 'Rig' paper
--  * Reflect universe levels back into the type system a.la. Agda
--  * Build an awesome programming language with this.
--  * Cubical types.




-- First off, declare some syntax forms.
-- These are always in normal form. This sidesteps the enormous headache of
-- equivalence types and coercions but means we need to do things like split
-- Elim and Term into seperate things (and Form and Type) to avoid having
-- multiple ways of representing the same term.

-- Contexts
data Ctx : Set

-- Universe levels. These are just natural numbers for now. Eventually I'd like
-- these to be reflected back into the type system somehow.
data Level : Set

-- Type formers (eg. Unit, Sigma, Pi etc.)
data Form : Ctx -> Level -> Set

-- Types. Embeds type formers but also includes the ability to forms types with
-- eliminators and through weakening.
data Type : Ctx -> Level -> Set

-- Proofs that a type is in a context. Used for substitutions.
data In : (c : Ctx) -> {cv : Ctx} -> {lv : Level} -> (Type cv lv) -> Set

-- Elimation terms. These are seperated from terms so that we can keep
-- everything in normal form. For example, for the term
-- (funcApplication someFunction someArg) we need someFunction to not be a
-- lambda, otherwise the term would be reducable. So lambdas live in the
-- type Term, not Elim.
data Elim : (c : Ctx) -> (l : Level) -> Type c l -> Set

-- Terms. Includes embeddings for type formers and eliminators,
data Term : (c : Ctx) -> (l : Level) -> Type c l -> Set




-- Substitution functions.
-- Substitute a term for some variable. One function for each syntax form.

substituteCtx : (cr : Ctx)
             -> {cv : Ctx}
             -> {lv : Level}
             -> {rv : Type cv lv}
             -> (tv : Term cv lv rv)
             -> (i : In cr rv)
             -> Ctx
substituteForm : {cf : Ctx}
              -> {lf : Level}
              -> Form cf lf
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Type cv lv}
              -> (tv : Term cv lv rv)
              -> (i : In cf rv)
              -> Form (substituteCtx cf tv i) lf
substituteType : {cr : Ctx}
              -> {lr : Level}
              -> Type cr lr
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Type cv lv}
              -> (tv : Term cv lv rv)
              -> (i : In cr rv)
              -> Type (substituteCtx cr tv i) lr
substituteTerm : {ct : Ctx}
              -> {lt : Level}
              -> {rt : Type ct lt}
              -> Term ct lt rt
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Type cv lv}
              -> (tv : Term cv lv rv)
              -> (i : In ct rv)
              -> Term (substituteCtx ct tv i) lt (substituteType rt tv i)
substituteElim : {ce : Ctx}
              -> {le : Level}
              -> {re : Type ce le}
              -> Elim ce le re
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Type cv lv}
              -> (tv : Term cv lv rv)
              -> (i : In ce rv)
              -> Term (substituteCtx ce tv i) le (substituteType re tv i)

data Ctx where
    CNil : Ctx
    CCons : (c : Ctx) -> (l : Level) -> Type c l -> Ctx

data Level where
    LZero : Level
    LSucc : Level -> Level

lmax : Level -> Level -> Level
lmax LZero b = LSucc b
lmax (LSucc a) LZero = LSucc a
lmax (LSucc a) (LSucc b) = LSucc (lmax a b)

data Form where
    -- The type of types.
    FType : {c : Ctx}
         -> (l : Level)
         -> Form c (LSucc l)
    -- The empty/bottom/zero/never type
    FNever : {c : Ctx}
          -> {l : Level}
          -> Form c l
    -- The unit type
    FUnit : {c : Ctx}
         -> {l : Level}
         -> Form c l
    -- Function (aka pi) types
    FFunc : {c : Ctx}
         -> {la : Level}
         -> (ra : Type c la)
         -> {lb : Level}
         -> Type (CCons c la ra) lb
         -> Form c (lmax la lb)
    -- Pair (aka sigma) types
    {-
    FPair : {c : Ctx}
         -> {lh : Level}
         -> (rh : Type c lh)
         -> {lt : Level}
         -> Type (CCons c lh rh) lt
         -> Form c (lmax lh lt)
    -}

data Type where
    -- Form a type from a type-former.
    RForm : {c : Ctx}
         -> {l : Level}
         -> Form c l
         -> Type c l

    -- Form a type from an elimination of type type.
    RElim : {c : Ctx}
         -> {l : Level}
         -> Elim c (LSucc l) (RForm (FType l))
         -> Type c l

{-
weakenForm : {c : Ctx}
          -> {l : Level}
          -> {ld : Level}
          -> {rd : Type c ld}
          -> Form c l
          -> Form (CCons c ld rd) l
weakenForm (FType l) = FType l
weakenForm FNever = FNever
weakenForm FUnit = FUnit
weakenForm (FFunc ra rb) = FFunc (weakenForm ra) (weakenForm rb)

weakenType : {c : Ctx}
          -> {l : Level}
          -> {ld : Level}
          -> {rd : Type c ld}
          -> Type c l
          -> Type (CCons c ld rd) l
weakenType (RForm f) = RForm (weakenForm f)
weakenType (RElim e) = RElim (weakenElim e)
    -- should be able to fix this by splitting Term into Term and Intro
    -- or maybe not
    -- 
-}


data In where
    -- The type in question is at the top of the context.
    ITop : {c : Ctx}
        -> {lv : Level}
        -> {rv : Type c lv}
        -> In (CCons c lv rv) rv
    -- The type is somewhere deeper in the context
    IPop : {c : Ctx}
        -> {ld : Level}
        -> {rd : Type c ld}
        -> {cv : Ctx}
        -> {lv : Level}
        -> {rv : Type cv lv}
        -> In c rv
        -> In (CCons c ld rd) rv

substituteCtx (CCons cr lv rv) tv ITop = cr
substituteCtx (CCons cr ld rd) tv (IPop i) = CCons (substituteCtx cr tv i) ld (substituteType rd tv i)




-- These "broaden" functions are used in the definition of the "reorder" functions later.


-- If a context contains a variable of type rx, and it contains a variable of
-- type ry before rx, then the context produced by substituting a term at rx
-- still contains ry
broadenPost : {c : Ctx}
           -> {cx : Ctx}
           -> {lx : Level}
           -> {rx : Type cx lx}
           -> {tx : Term cx lx rx}
           -> (ix : In c rx)
           -> {cy : Ctx}
           -> {ly : Level}
           -> {ry : Type cy ly}
           -> (iy : In cx ry)
           -> In (substituteCtx c tx ix) ry
broadenPost ITop iy = iy
broadenPost (IPop ix) iy = IPop (broadenPost ix iy)

-- If a context contains a variable of type rx, and it contains a variable of
-- type ry before rx, then the context as a whole contains an ry.
broadenPre : {c : Ctx}
          -> {cx : Ctx}
          -> {lx : Level}
          -> {rx : Type cx lx}
          -> {tx : Term cx lx rx}
          -> (ix : In c rx)
          -> {cy : Ctx}
          -> {ly : Level}
          -> {ry : Type cy ly}
          -> (iy : In cx ry)
          -> In c ry
broadenPre ITop iy = IPop iy
broadenPre (IPop ix) iy = IPop (broadenPre ix iy)

-- If a context contains a variable of type rx, and it contains a variable of
-- type ry before rx, then the context produced by substituting a term at ry
-- contains a variable whose type is rx substituted with the term at ry.
broadenStill : {c : Ctx}
            -> {cx : Ctx}
            -> {lx : Level}
            -> {rx : Type cx lx}
            -> {tx : Term cx lx rx}
            -> (ix : In c rx)
            -> {cy : Ctx}
            -> {ly : Level}
            -> {ry : Type cy ly}
            -> {ty : Term cy ly ry}
            -> (iy : In cx ry)
            -> In (substituteCtx c ty (broadenPre ix iy)) (substituteType rx ty iy)
broadenStill ITop iy = ITop
broadenStill (IPop ix) iy = IPop (broadenStill ix iy)



-- Substitutions on contexts are stable under reordering.
reorderCtx : {c : Ctx}
          -> {cx : Ctx}
          -> {lx : Level}
          -> {rx : Type cx lx}
          -> {tx : Term cx lx rx}
          -> (ix : In c rx)
          -> {cy : Ctx}
          -> {ly : Level}
          -> {ry : Type cy ly}
          -> {ty : Term cy ly ry}
          -> (iy : In cx ry)
          -> (substituteCtx (substituteCtx c tx ix) ty (broadenPost ix iy)) ≡
             (substituteCtx (substituteCtx c ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy))

-- Substitutions on types are stable under reordering.
reorderType : {c : Ctx}
           -> {l : Level}
           -> {r : Type c l}
           -> {cx : Ctx}
           -> {lx : Level}
           -> {rx : Type cx lx}
           -> {tx : Term cx lx rx}
           -> (ix : In c rx)
           -> {cy : Ctx}
           -> {ly : Level}
           -> {ry : Type cy ly}
           -> {ty : Term cy ly ry}
           -> (iy : In cx ry)
           -> (substituteType (substituteType r tx ix) ty (broadenPost ix iy)) ===
              (substituteType (substituteType r ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy))

-- Substitutions on type formers are stable under reordering.
reorderForm : {c : Ctx}
           -> {l : Level}
           -> {f : Form c l}
           -> {cx : Ctx}
           -> {lx : Level}
           -> {rx : Type cx lx}
           -> {tx : Term cx lx rx}
           -> (ix : In c rx)
           -> {cy : Ctx}
           -> {ly : Level}
           -> {ry : Type cy ly}
           -> {ty : Term cy ly ry}
           -> (iy : In cx ry)
           -> (substituteForm (substituteForm f tx ix) ty (broadenPost ix iy)) ===
              (substituteForm (substituteForm f ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy))

-- Substitutions on eliminations are stable under reordering.
reorderElim : {c : Ctx}
           -> {l : Level}
           -> {r : Type c l}
           -> {e : Elim c l r}
           -> {cx : Ctx}
           -> {lx : Level}
           -> {rx : Type cx lx}
           -> {tx : Term cx lx rx}
           -> (ix : In c rx)
           -> {cy : Ctx}
           -> {ly : Level}
           -> {ry : Type cy ly}
           -> {ty : Term cy ly ry}
           -> (iy : In cx ry)
           -> (substituteTerm (substituteElim e tx ix) ty (broadenPost ix iy)) ===
              (substituteTerm (substituteElim e ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy))

-- Substitutions on terms are stable under reordering.
reorderTerm : {c : Ctx}
           -> {l : Level}
           -> {r : Type c l}
           -> {t : Term c l r}
           -> {cx : Ctx}
           -> {lx : Level}
           -> {rx : Type cx lx}
           -> {tx : Term cx lx rx}
           -> (ix : In c rx)
           -> {cy : Ctx}
           -> {ly : Level}
           -> {ry : Type cy ly}
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
    let srdXY : Type scXY ld
        srdXY = substituteType (substituteType rd tx ix) ty (broadenPost ix iy)
    in
    let srdYX : Type scYX ld
        srdYX = substituteType (substituteType rd ty (broadenPre ix iy)) (substituteTerm tx ty iy) (broadenStill ix iy)
    in
    let resrd : srdXY === srdYX
        resrd = reorderType ix iy
    in
    let bong : (CCons scXY ld srdXY) === (CCons scYX ld srdYX)
        bong = cong3Het CCons flooz refl resrd
    in
    heteroToHomo bong


intoType : {c : Ctx}
        -> {l : Level}
        -> Term c (LSucc l) (RForm (FType l)) -> Type c l


substituteForm (FType l) tv i = FType l
substituteForm FNever tv i = FNever
substituteForm FUnit tv i = FUnit
substituteForm (FFunc ra rb) tv i = FFunc (substituteType ra tv i) (substituteType rb tv (IPop i))
--substituteForm (FPair rh rt) tv i = FPair (substituteType rh tv i) (substituteType rt tv (IPop i))

substituteType (RForm f) tv i = RForm (substituteForm f tv i)
substituteType (RElim e) tv i = intoType (substituteElim e tv i)


reorderForm {_} {_} {FType l} ITop iy = refl
reorderForm {_} {_} {FType l} (IPop ix) iy = refl
reorderForm {c} {l} {FNever} ITop iy = refl
reorderForm {c} {l} {FNever} (IPop ix) iy = refl
reorderForm {c} {l} {FUnit} ITop iy = refl
reorderForm {c} {l} {FUnit} (IPop ix) iy = refl
reorderForm {c} {_} {FFunc ra rb} ITop iy =
    cong2ImplHet (reorderForm ITop iy) (reorderForm (IPop ITop) iy)
reorderForm {c} {_} {FFunc ra rb} (IPop ix) iy =
    cong2ImplHet (reorderForm (IPop ix) iy) (reorderForm (IPop (IPop ix)) iy)
{-
reorderForm {c} {_} {FPair rh rt} ITop iy =
    cong2ImplHet (reorderForm ITop iy) (reorderForm (IPop ITop) iy)
reorderForm {c} {_} {FPair rh rt} (IPop ix) iy =
    cong2ImplHet (reorderForm (IPop ix) iy) (reorderForm (IPop (IPop ix)) iy)
-}

reorderType {_} {_} {RForm x} ITop iy =
    cong1ImplHet (reorderForm ITop iy)
reorderType {_} {_} {RForm x} (IPop ix) iy =
    cong1ImplHet (reorderForm (IPop ix) iy)
reorderType {_} {l} {RElim x} ITop iy =
    cong1ImplHet (reorderElim ITop iy)
reorderType {_} {l} {RElim x} (IPop ix) iy =
    cong1ImplHet (reorderElim (IPop ix) iy)
    


-- A term of type never must be an elimination.
neverElim : {c : Ctx}
         -> {l : Level}
         -> Term c l (RForm FNever)
         -> Elim c l (RForm FNever)

-- Apply a function term to an argument term to get the resulting term.
tapp : {c : Ctx}
    -> {la : Level}
    -> {ra : Type c la}
    -> {lb : Level}
    -> {rb : Type (CCons c la ra) lb}
    -> Term c (lmax la lb) (RForm (FFunc ra rb))
    -> (ta : Term c la ra)
    -> Term c lb (substituteType rb ta ITop)

{-
tbust : {c : Ctx}
     -> {lh : Level}
     -> {rh : Type c lh}
     -> {lt : Level}
     -> {rt : Type (CCons c lh rh) lt}
     -> (tp : Term c (lmax lh lt) (RForm (FPair rh rt)))
     -> {lb : Level}
     -> {rb : Type (CCons c (lmax lh lt) (RForm (FPair rh rt))) lb}
     -> (tr : Term (CCons c (lmax lh lt) (RForm (FPair rh rt))) lb rb)
     -> Term c lb (substituteType rb tp ITop)
-}

data Term where
    -- The unit term.
    TUnit : {c : Ctx}
         -> Term c LZero (RForm FUnit)

    -- Lambda.
    TFunc : {c : Ctx}
         -> {la : Level}
         -> {ra : Type c la}
         -> {lb : Level}
         -> {rb : Type (CCons c la ra) lb}
         -> Term (CCons c la ra) lb rb
         -> Term c (lmax la lb) (RForm (FFunc ra rb))

    -- A pair.
    {-
    TPair : {c : Ctx}
         -> {lh : Level}
         -> {rh : Type c lh}
         -> {lt : Level}
         -> {rt : Type (CCons c lh rh) lt}
         -> (th : Term c lh rh)
         -> (tt : Term c lt (substituteType rt th ITop))
         -> Term c (lmax lh lt) (RForm (FPair rh rt))
    -}

    -- Embed a type-former. We use Form here rather than Type because otherwise
    -- (TEmbedElim e) and (TEmbedType (RElim e)) would be the same thing and we
    -- want to keep everything normalised.
    TEmbedForm : {c : Ctx}
              -> {l : Level}
              -> Form c l
              -> Term c (LSucc l) (RForm (FType l))

    -- Embed an elimination term.
    TEmbedElim : {c : Ctx}
              -> {l : Level}
              -> {r : Type c l}
              -> Elim c l r
              -> Term c l r

{-
typeToTerm : {c : Ctx}
          -> {l : Level}
          -> {r : Type c l}
          -> Term c (LSucc l) (RForm (FType l))
typeToTerm (RForm f) = TEmbedForm f
-}

data Weakenable : (c : Ctx)
               -> {cd : Ctx}
               -> {ld : Level}
               -> (rd : Type cd ld)
               -> Set

data Weakenable where
    WTop : {c : Ctx}
        -> {ld : Level}
        -> {rd : Type c ld}
        -> Weakenable c rd
    WPop : {c : Ctx}
        -> {cd : Ctx}
        -> {ld : Level}
        -> {rd : Type cd ld}
        -> {lt : Level}
        -> {rt : Type c lt}
        -> Weakenable c rd
        -> Weakenable (CCons c lt rt) rd

weakenCtx : {cd : Ctx}
         -> {ld : Level}
         -> {rd : Type cd ld}
         -> (c : Ctx)
         -> (w : Weakenable c rd)
         -> Ctx

weakenForm : {cd : Ctx}
          -> {ld : Level}
          -> {rd : Type cd ld}
          -> {c : Ctx}
          -> {l : Level}
          -> (f : Form c l)
          -> (w : Weakenable c rd)
          -> Form (weakenCtx c w) l

weakenType : {cd : Ctx}
          -> {ld : Level}
          -> {rd : Type cd ld}
          -> {c : Ctx}
          -> {l : Level}
          -> (r : Type c l)
          -> (w : Weakenable c rd)
          -> Type (weakenCtx c w) l

weakenElim : {cd : Ctx}
          -> {ld : Level}
          -> {rd : Type cd ld}
          -> {c : Ctx}
          -> {l : Level}
          -> {r : Type c l}
          -> (e : Elim c l r)
          -> (w : Weakenable c rd)
          -> Elim (weakenCtx c w) l (weakenType r w)

weakenTerm : {cd : Ctx}
          -> {ld : Level}
          -> {rd : Type cd ld}
          -> {c : Ctx}
          -> {l : Level}
          -> {r : Type c l}
          -> (t : Term c l r)
          -> (w : Weakenable c rd)
          -> Term (weakenCtx c w) l (weakenType r w)


{-
weakenIn : {cd : Ctx}
        -> {ld : Level}
        -> {rd : Type cd ld}
        -> {c : Ctx}
        -> {cv : Ctx}
        -> {lv : Level}
        -> {rv : Type cv lv}
        -> In c rv
        -> (w : Weaken c rd)
        -> In (weakenCtx 
-}

weakenCtx {ld = ld} {rd = rd} c WTop = CCons c ld rd
weakenCtx (CCons c lt rt) (WPop w) = CCons (weakenCtx c w) lt (weakenType rt w)

data UndoWeaken : {c : Ctx}
               -> {cv : Ctx}
               -> {lv : Level}
               -> {rv : Type cv lv}
               -> (w : Weakenable c rv)
               -> In (weakenCtx c w) rv
               -> Set

data UndoWeaken where
    UTop : UndoWeaken WTop ITop
    UPop : {c : Ctx}
        -> {cv : Ctx}
        -> {lv : Level}
        -> {rv : Type cv lv}
        -> {w : Weakenable c rv}
        -> {i : In (weakenCtx c w) rv}
        -> UndoWeaken w i
        -> UndoWeaken (WPop w) (IPop i)

{-
weakSubTopCtx : (c : Ctx)
             -> {lv : Level}
             -> {rv : Type c lv}
             -> {tv : Term c lv rv}
             -> (substituteCtx (weakenCtx c (WTop {c} {lv} {rv})) tv ITop) ≡ c

weakSubTopCtx c = refl
-}

undoWeakenCtx : (c : Ctx)
             -> {cv : Ctx}
             -> {lv : Level}
             -> {rv : Type cv lv}
             -> {tv : Term cv lv rv}
             -> {w : Weakenable c rv}
             -> {i : In (weakenCtx c w) rv}
             -> UndoWeaken w i
             -> c === (substituteCtx (weakenCtx c w) tv i)

weakenForm (FType l) w = FType l
weakenForm FNever w = FNever
weakenForm FUnit w = FUnit
weakenForm (FFunc ra rb) w = FFunc (weakenType ra w) (weakenType rb (WPop w))
--weakenForm (FPair rh rt) w = FPair (weakenType rh w) (weakenType rt (WPop w))

weakenType (RForm f) w = RForm (weakenForm f w)
weakenType (RElim e) w = RElim (weakenElim e w)

undoWeakenType : {c : Ctx}
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Type cv lv}
              -> {tv : Term cv lv rv}
              -> {l : Level}
              -> (r : Type c l)
              -> {w : Weakenable c rv}
              -> {i : In (weakenCtx c w) rv}
              -> UndoWeaken w i
              -> r === (substituteType (weakenType r w) tv i)

undoWeakenCtx c UTop = refl
undoWeakenCtx (CCons c lt rt) {cv} {lv} {rv} {tv} {WPop w} {IPop i} (UPop u) =
    let aa : (c === (substituteCtx (weakenCtx c w) tv i))
        aa = (undoWeakenCtx c u)
    in
    let bb : ((CCons c lt rt) === (CCons (substituteCtx (weakenCtx c w) tv i) lt (substituteType (weakenType rt w) tv i)))
        bb = cong3Het CCons aa refl (undoWeakenType rt u)
    in
    bb

undoWeakenType r u = ?

extractType : {c : Ctx}
           -> {cv : Ctx}
           -> {lv : Level}
           -> {rv : Type cv lv}
           -> In c rv
           -> Type c lv
extractType {_} {_} {_} {rv} ITop = weakenType rv WTop
extractType (IPop i) = weakenType (extractType i) WTop


data Elim where
    -- Grad the inner-most variable from the context.
    EVar : {c : Ctx}
        -> {cv : Ctx}
        -> {lv : Level}
        -> {rv : Type cv lv}
        -> (i : In c rv)
        -> Elim c lv (extractType i)

    -- Eliminator for the never type.
    EAbort : {c : Ctx}
          -> Elim c LZero (RForm FNever)
          -> {lr : Level}
          -> (r : Type c lr)
          -> Elim c lr r

    -- Function application
    EFunc : {c : Ctx}
         -> {la : Level}
         -> {ra : Type c la}
         -> {lb : Level}
         -> {rb : Type (CCons c la ra) lb}
         -> (ef : Elim c (lmax la lb) (RForm (FFunc ra rb)))
         -> (ta : Term c la ra)
         -> Elim c lb (substituteType rb ta ITop)

    {-
    EPair : {c : Ctx}
         -> {lh : Level}
         -> {rh : Type c lh}
         -> {lt : Level}
         -> {rt : Type (CCons c lh rh) lt}
         -> (ep : Elim c (lmax lh lt) (RForm (FPair rh rt)))
         -> {lb : Level}
         -> {rb : Type (CCons (CCons c lh rh) lt rt) lb}
         -> (tb : Term (CCons (CCons c lh rh) lt rt) lb rb)
         -> Elim c lb (RElim (EPair ep (typeToTerm rb)))
    -}


neverElim (TEmbedElim e) = e

tapp (TFunc rb) ta = substituteTerm rb ta ITop
tapp (TEmbedElim ef) ta = TEmbedElim (EFunc ef ta)

--tbust (TPair th tt) tb = substituteTerm 

intoType (TEmbedForm f) = RForm f
intoType (TEmbedElim e) = RElim e

--substituteElim {.(CCons cv lv rv)} {.lv} {.(extractType ITop)} (EVar {.(CCons cv lv rv)} {.cv} {.lv} {.rv} (ITop {.cv} {.lv} {.rv})) {cv} {lv} {rv} tv (ITop {,cv} {,lv} {,rv}) = tv
substituteElim (EVar ITop) {cv} {lv} {rv} tv ITop =
    {-
    let typeTrans : rv === substituteType (weakenType rv WTop) tv ITop
        typeTrans = undoWeakenType rv (UTop {})
    in
    let wub : Term cv lv rv === Term cv lv (substituteType (weakenType rv WTop) tv ITop)
        wub = cong1Het (Term cv lv) typeTrans
    in
    transport (heteroToHomo wub) tv
    -}
    ?
substituteElim (EVar (IPop j)) tv ITop = ? -- TEmbedElim (EVar j)
substituteElim (EVar ITop) tv (IPop i) = ? -- TEmbedElim (EVar ITop)
substituteElim (EVar (IPop j)) tv (IPop i) = ? --weakenTerm (substituteElim (EVar j) tv i) WTop
substituteElim (EAbort en rb) tv i =
    let sen = neverElim (substituteElim en tv i) in
    let srb = substituteType rb tv i in
    TEmbedElim (EAbort sen srb)
substituteElim (EFunc ef ta) tv i =
    let stf = substituteElim ef tv i in
    let sta = substituteTerm ta tv i in
    let got = tapp stf sta in
    let same0 = reorderType ITop i in
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



substituteTerm TUnit tv i = TUnit
substituteTerm (TFunc tb) tv i = 
    let stb = substituteTerm tb tv (IPop i) in
    TFunc stb
{-
substituteTerm (TPair th tt) tv i =
    let sth = substituteTerm th tv i in
    let stt = substituteTerm tt tv i in
    let same0 = reorderType ITop i in
    let same1 = cong1ImplHet same0 in
    let same2 = heteroToHomo same1 in
    TPair sth (transport same2 stt)
-}
substituteTerm (TEmbedForm f) tv i = TEmbedForm (substituteForm f tv i)
substituteTerm (TEmbedElim e) tv i = substituteElim e tv i

reorderElim {_} {_} {_} {EVar ITop} ITop iy = ? -- refl
reorderElim {_} {_} {_} {EVar (IPop j)} ITop iy = ?
reorderElim {_} {_} {_} {EVar ITop} (IPop ix) iy = ?
reorderElim {_} {_} {_} {EVar (IPop j)} (IPop ix) iy = ?
reorderElim {_} {_} {_} {EAbort e r} ITop iy =
    cong2ImplHet (cong1Het neverElim (reorderElim ITop iy)) (reorderType ITop iy)
reorderElim {_} {_} {_} {EAbort e r} (IPop ix) iy =
    cong2ImplHet (cong1Het neverElim (reorderElim (IPop ix) iy)) (reorderType (IPop ix) iy)
reorderElim {_} {_} {_} {EFunc e ta} ITop iy =
    cong2ImplHet (reorderElim ITop iy) (reorderTerm ITop iy)
reorderElim {_} {_} {_} {EFunc e ta} (IPop ix) iy = ?
    cong2ImplHet (reorderElim (IPop ix) iy) (reorderTerm (IPop ix) iy)

reorderTerm {_} {_} {_} {TUnit} ITop iy = refl
reorderTerm {_} {_} {_} {TUnit} (IPop ix) iy = refl
reorderTerm {_} {_} {_} {TFunc tb} ITop iy = 
    cong1ImplHet (reorderTerm ITop iy)
reorderTerm {_} {_} {_} {TFunc tb} (IPop ix) iy =
    cong1ImplHet (reorderTerm (IPop ix) iy)
{-
reorderTerm {_} {_} {_} {TPair th tt} ITop iy =
    cong2ImplHet (reorderTerm ITop iy) (reorderTerm ITop iy)
reorderTerm {_} {_} {_} {TPair tt th} (IPop ix) iy =
    cong2ImplHet (reorderTerm (IPop ix) iy) (reorderTerm (IPop ix) iy)
-}
reorderTerm {_} {_} {_} {TEmbedForm f} ITop iy =
    cong1ImplHet (reorderForm ITop iy)
reorderTerm {_} {_} {_} {TEmbedForm f} (IPop ix) iy =
    cong1ImplHet (reorderForm (IPop ix) iy)
reorderTerm {_} {_} {_} {TEmbedElim e} ITop iy =
    reorderElim ITop iy
reorderTerm {_} {_} {_} {TEmbedElim e} (IPop ix) iy =
    reorderElim (IPop ix) iy



weakenElim (EVar i) w = EVar ?
weakenElim (EAbort ev r) w = EAbort (weakenElim ev w) (weakenType r w)
weakenElim (EFunc ef ta) w = ? -- EFunc (weakenElim ef w) (weakenTerm ta w)

undoWeakenElim : {c : Ctx}
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Type cv lv}
              -> {tv : Term cv lv rv}
              -> {l : Level}
              -> {r : Type c l}
              -> (e : Elim c l r)
              -> {w : Weakenable c rv}
              -> {i : In (weakenCtx c w) rv}
              -> UndoWeaken w i
              -> e === (substituteElim (weakenElim e w) tv i)

undoWeakenElim e u = ?

weakenTerm TUnit w = TUnit
weakenTerm (TFunc ta) w = TFunc (weakenTerm ta (WPop w))
--weakenTerm (TPair th tt) w = TPair (weakenTerm th w) (weakenTerm tt w)
weakenTerm (TEmbedForm f) w = TEmbedForm (weakenForm f w)
weakenTerm (TEmbedElim e) w = TEmbedElim (weakenElim e w)

undoWeakenTerm : {c : Ctx}
              -> {cv : Ctx}
              -> {lv : Level}
              -> {rv : Type cv lv}
              -> {tv : Term cv lv rv}
              -> {l : Level}
              -> {r : Type c l}
              -> (t : Term c l r)
              -> {w : Weakenable c rv}
              -> {i : In (weakenCtx c w) rv}
              -> UndoWeaken w i
              -> t === (substituteTerm (weakenTerm t w) tv i)

undoWeakenTerm t u = ?

