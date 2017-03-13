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

