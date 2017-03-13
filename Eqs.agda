module Eqs where

open import Agda.Builtin.Equality public
infix 4 _===_

data _===_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
    refl : x === x

cong1Het : ∀ {a b} {A : Set a} {B : A → Set b}
          {x y}
        (f : (x : A) -> B x) → x === y → f x === f y
cong1Het f refl = refl

cong1ImplHet : ∀ {a b} {A : Set a} {B : A → Set b}
          {x y}
        {f : (x : A) -> B x} → x === y → f x === f y
cong1ImplHet refl = refl

cong2Het : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {x y u v}
        (f : (x : A) (y : B x) → C x y) → x === y → u === v → f x u === f y v
cong2Het f refl refl = refl

cong2ImplHet : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {x y u v}
        {f : (x : A) (y : B x) → C x y} → x === y → u === v → f x u === f y v
cong2ImplHet refl refl = refl

cong3Het : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x -> ∀ y -> C x y -> Set d}
          {x y u v p q}
        (f : (x : A) (y : B x) → (z : C x y) -> D x y z) → x === y → u === v → p === q -> f x u p === f y v q
cong3Het f refl refl refl = refl

heteroToHomo : forall {lla}
            -> {a : Set lla}
            -> {x0 : a}
            -> {x1 : a}
            -> x0 === x1
            -> x0 ≡ x1
heteroToHomo refl = refl

homoToHetero : forall {lla}
            -> {a : Set lla}
            -> {x0 : a}
            -> {x1 : a}
            -> x0 ≡ x1
            -> x0 === x1
homoToHetero refl = refl


transport : forall {ll}
         -> {a : Set ll}
         -> {b : Set ll}
         -> a ≡ b
         -> a
         -> b
transport refl x = x

eqFunc : forall {lla llb}
      -> {a : Set lla}
      -> {b : a -> Set llb}
      -> {f0 : (x : a) -> b x}
      -> {f1 : (x : a) -> b x}
      -> f0 ≡ f1
      -> (x : a)
      -> (f0 x) ≡ (f1 x)
eqFunc refl x = refl

explicitEq : forall {ll}
          -> (a : Set ll)
          -> (x : a)
          -> (y : a)
          -> Set ll
explicitEq a x y = x ≡ y

eqFuncImplicit : forall {lla llb}
              -> {a : Set lla}
              -> {b : a -> Set llb}
              -> {f0 : {x : a} -> b x}
              -> {f1 : {x : a} -> b x}
              -- -> f0 ≡ f1
              -- -> explicitEq ({x : a} -> b x) f0 f1
              -> (_≡_) {A = {x : a} -> b x} f0 f1
              -> (x : a)
              -> (f0 {x}) ≡ (f1 {x})
eqFuncImplicit refl x = refl

eqArgNonDep : forall {lla}
           -> forall {llb}
           -> {a : Set lla}
           -> {b : Set llb}
           -> (f : a -> b)
           -> {x0 : a}
           -> {x1 : a}
           -> x0 ≡ x1
           -> (f x0) ≡ (f x1)
eqArgNonDep f refl = refl

eqArg : forall {lla}
     -> forall {llb}
     -> {a : Set lla}
     -> {b : a -> Set llb}
     -> (f : (x : a) -> b x)
     -> {x0 : a}
     -> {x1 : a}
     -> (xq : x0 ≡ x1)
     -> (f x0) === (f x1)
eqArg f refl = refl

eqAppNonDep : {a : Set}
           -> {b : Set}
           -> {f0 : a -> b}
           -> {f1 : a -> b}
           -> {x0 : a}
           -> {x1 : a}
           -> (fq : f0 ≡ f1)
           -> (xq : x0 ≡ x1)
           -> (f0 x0) ≡ (f1 x1)
eqAppNonDep refl refl = refl

eqApp : {a : Set}
     -> {b : a -> Set}
     -> {f0 : (x : a) -> b x}
     -> {f1 : (x : a) -> b x}
     -> {x0 : a}
     -> {x1 : a}
     -> (fq : f0 ≡ f1)
     -> (xq : x0 ≡ x1)
     -> (f0 x0) === (f1 x1)
eqApp refl refl = refl

eqAppHet : forall {lla llb}
        -> {a0 : Set lla}
        -> {a1 : Set lla}
        -> {b0 : a0 -> Set llb}
        -> {b1 : a1 -> Set llb}
        -> {f0 : (x : a0) -> b0 x}
        -> {f1 : (x : a1) -> b1 x}
        -> {x0 : a0}
        -> {x1 : a1}
        -> a0 ≡ a1
        -> b0 === b1
        -> f0 === f1
        -> x0 === x1
        -> (f0 x0) === (f1 x1)
eqAppHet refl refl refl refl = refl


