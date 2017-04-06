module Eqs where

open import Agda.Builtin.Equality public
infix 4 _===_

data _===_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
    refl : x === x

cong1Het : forall {l0 r}
           {T0 : Set l0}
           {R : T0 -> Set r}
           {x0 y0}
           (f : (a0 : T0) -> R a0)
           -> x0 === y0
           -> f x0 === f y0
cong1Het f refl = refl

cong2Het : forall {l0 l1 r}
           {T0 : Set l0}
           {T1 : T0 -> Set l1}
           {R : (a0 : T0) -> (T1 a0) -> Set r}
           {x0 y0 x1 y1}
           (f : (a0 : T0) -> (a1 : T1 a0) -> R a0 a1)
           -> x0 === y0
           -> x1 === y1
           -> f x0 x1 === f y0 y1
cong2Het f refl refl = refl

cong2HetAiAe : forall {l0 l1 r}
               {T0 : Set l0}
               {T1 : T0 -> Set l1}
               {R : (a0 : T0) -> (T1 a0) -> Set r}
               {x0 y0 x1 y1}
               (f : {a0 : T0} -> (a1 : T1 a0) -> R a0 a1)
               -> x0 === y0
               -> x1 === y1
               -> f {x0} x1 === f {y0} y1
cong2HetAiAe f refl refl = refl

cong2HetAiAi : forall {l0 l1 r}
               {T0 : Set l0}
               {T1 : T0 -> Set l1}
               {R : (a0 : T0) -> (T1 a0) -> Set r}
               {x0 y0 x1 y1}
               (f : {a0 : T0} -> {a1 : T1 a0} -> R a0 a1)
               -> x0 === y0
               -> x1 === y1
               -> f {x0} {x1} === f {y0} {y1}
cong2HetAiAi f refl refl = refl

cong3Het : forall {l0 l1 l2 r}
           {T0 : Set l0}
           {T1 : T0 -> Set l1}
           {T2 : (a0 : T0) -> (T1 a0) -> Set l2}
           {R : (a0 : T0) -> (a1 : T1 a0) -> (T2 a0 a1) -> Set r}
           {x0 y0 x1 y1 x2 y2}
           (f : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> R a0 a1 a2)
           -> x0 === y0
           -> x1 === y1
           -> x2 === y2
           -> f x0 x1 x2 === f y0 y1 y2
cong3Het f refl refl refl = refl

cong3HetAiAeAe : forall {l0 l1 l2 r}
                 {T0 : Set l0}
                 {T1 : T0 -> Set l1}
                 {T2 : (a0 : T0) -> (T1 a0) -> Set l2}
                 {R : (a0 : T0) -> (a1 : T1 a0) -> (T2 a0 a1) -> Set r}
                 {x0 y0 x1 y1 x2 y2}
                 (f : {a0 : T0} -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> R a0 a1 a2)
                 -> x0 === y0
                 -> x1 === y1
                 -> x2 === y2
                 -> f {x0} x1 x2 === f {y0} y1 y2
cong3HetAiAeAe f refl refl refl = refl

cong4Het : forall {l0 l1 l2 l3 r}
           {T0 : Set l0}
           {T1 : T0 -> Set l1}
           {T2 : (a0 : T0) -> (T1 a0) -> Set l2}
           {T3 : (a0 : T0) -> (a1 : T1 a0) -> (T2 a0 a1) -> Set l3}
           {R : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (T3 a0 a1 a2) -> Set r}
           {x0 y0 x1 y1 x2 y2 x3 y3}
           (f : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (a3 : T3 a0 a1 a2) -> R a0 a1 a2 a3)
           -> x0 === y0
           -> x1 === y1
           -> x2 === y2
           -> x3 === y3
           -> f x0 x1 x2 x3 === f y0 y1 y2 y3
cong4Het f refl refl refl refl = refl

cong5Het : forall {l0 l1 l2 l3 l4 r}
           {T0 : Set l0}
           {T1 : T0 -> Set l1}
           {T2 : (a0 : T0) -> (T1 a0) -> Set l2}
           {T3 : (a0 : T0) -> (a1 : T1 a0) -> (T2 a0 a1) -> Set l3}
           {T4 : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (T3 a0 a1 a2) -> Set l4}
           {R : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (a3 : T3 a0 a1 a2) -> (T4 a0 a1 a2 a3) -> Set r}
           {x0 y0 x1 y1 x2 y2 x3 y3 x4 y4}
           (f : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (a3 : T3 a0 a1 a2) -> (a4 : T4 a0 a1 a2 a3) -> R a0 a1 a2 a3 a4)
           -> x0 === y0
           -> x1 === y1
           -> x2 === y2
           -> x3 === y3
           -> x4 === y4
           -> f x0 x1 x2 x3 x4 === f y0 y1 y2 y3 y4
cong5Het f refl refl refl refl refl = refl

cong5HetAiAiAeAiAe : forall {l0 l1 l2 l3 l4 r}
                     {T0 : Set l0}
                     {T1 : T0 -> Set l1}
                     {T2 : (a0 : T0) -> (T1 a0) -> Set l2}
                     {T3 : (a0 : T0) -> (a1 : T1 a0) -> (T2 a0 a1) -> Set l3}
                     {T4 : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (T3 a0 a1 a2) -> Set l4}
                     {R : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (a3 : T3 a0 a1 a2) -> (T4 a0 a1 a2 a3) -> Set r}
                     {x0 y0 x1 y1 x2 y2 x3 y3 x4 y4}
                     (f : {a0 : T0} -> {a1 : T1 a0} -> (a2 : T2 a0 a1) -> {a3 : T3 a0 a1 a2} -> (a4 : T4 a0 a1 a2 a3) -> R a0 a1 a2 a3 a4)
                     -> x0 === y0
                     -> x1 === y1
                     -> x2 === y2
                     -> x3 === y3
                     -> x4 === y4
                     -> f {x0} {x1} x2 {x3} x4 === f {y0} {y1} y2 {y3} y4
cong5HetAiAiAeAiAe f refl refl refl refl refl = refl

{-
cong1ImplHet : forall {l0 r}
               {T0 : Set l0}
               {R : T0 -> Set r}
               {x0 y0}
               {f : (a0 : T0) -> R a0}
               -> x0 === y0
               -> f x0 === f y0
cong1ImplHet refl = refl
-}

cong2ImplHet : forall {l0 l1 r}
               {T0 : Set l0}
               {T1 : T0 -> Set l1}
               {R : (a0 : T0) -> (T1 a0) -> Set r}
               {x0 y0 x1 y1}
               {f : (a0 : T0) -> (a1 : T1 a0) -> R a0 a1}
               -> x0 === y0
               -> x1 === y1
               -> f x0 x1 === f y0 y1
cong2ImplHet refl refl = refl

cong3ImplHet : forall {l0 l1 l2 r}
               {T0 : Set l0}
               {T1 : T0 -> Set l1}
               {T2 : (a0 : T0) -> (T1 a0) -> Set l2}
               {R : (a0 : T0) -> (a1 : T1 a0) -> (T2 a0 a1) -> Set r}
               {x0 y0 x1 y1 x2 y2}
               {f : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> R a0 a1 a2}
               -> x0 === y0
               -> x1 === y1
               -> x2 === y2
               -> f x0 x1 x2 === f y0 y1 y2
cong3ImplHet refl refl refl = refl

cong4ImplHet : forall {l0 l1 l2 l3 r}
               {T0 : Set l0}
               {T1 : T0 -> Set l1}
               {T2 : (a0 : T0) -> (T1 a0) -> Set l2}
               {T3 : (a0 : T0) -> (a1 : T1 a0) -> (T2 a0 a1) -> Set l3}
               {R : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (T3 a0 a1 a2) -> Set r}
               {x0 y0 x1 y1 x2 y2 x3 y3}
               {f : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (a3 : T3 a0 a1 a2) -> R a0 a1 a2 a3}
               -> x0 === y0
               -> x1 === y1
               -> x2 === y2
               -> x3 === y3
               -> f x0 x1 x2 x3 === f y0 y1 y2 y3
cong4ImplHet refl refl refl refl = refl

cong5ImplHet : forall {l0 l1 l2 l3 l4 r}
               {T0 : Set l0}
               {T1 : T0 -> Set l1}
               {T2 : (a0 : T0) -> (T1 a0) -> Set l2}
               {T3 : (a0 : T0) -> (a1 : T1 a0) -> (T2 a0 a1) -> Set l3}
               {T4 : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (T3 a0 a1 a2) -> Set l4}
               {R : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (a3 : T3 a0 a1 a2) -> (T4 a0 a1 a2 a3) -> Set r}
               {x0 y0 x1 y1 x2 y2 x3 y3 x4 y4}
               {f : (a0 : T0) -> (a1 : T1 a0) -> (a2 : T2 a0 a1) -> (a3 : T3 a0 a1 a2) -> (a4 : T4 a0 a1 a2 a3) -> R a0 a1 a2 a3 a4}
               -> x0 === y0
               -> x1 === y1
               -> x2 === y2
               -> x3 === y3
               -> x4 === y4
               -> f x0 x1 x2 x3 x4 === f y0 y1 y2 y3 y4
cong5ImplHet refl refl refl refl refl = refl


{-
cong1Het : ∀ {a b} {A : Set a} {B : A → Set b}
          {x y}
        (f : (x : A) -> B x) → x === y → f x === f y
cong1Het f refl = refl
-}

cong1ImplHet : ∀ {a b} {A : Set a} {B : A → Set b}
          {x y}
        {f : (x : A) -> B x} → x === y → f x === f y
cong1ImplHet refl = refl

{-
cong2Het : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {x y u v}
        (f : (x : A) (y : B x) → C x y) → x === y → u === v → f x u === f y v
cong2Het f refl refl = refl

cong2ImplHet : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {x y u v}
        {f : (x : A) (y : B x) → C x y} → x === y → u === v → f x u === f y v
cong2ImplHet refl refl = refl

cong2HetAiAe : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {x y u v}
        (f : {x : A} (y : B x) → C x y) → x === y → u === v → f {x} u === f {y} v
cong2HetAiAe f refl refl = refl

cong2HetAiAi : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {x y u v}
        (f : {x : A} {y : B x} → C x y) → x === y → u === v → f {x} {u} === f {y} {v}
cong2HetAiAi f refl refl = refl

cong3Het : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x -> ∀ y -> C x y -> Set d}
          {x y u v p q}
        (f : (x : A) (y : B x) → (z : C x y) -> D x y z) → x === y → u === v → p === q -> f x u p === f y v q
cong3Het f refl refl refl = refl

cong3HetAiAeAe : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x -> ∀ y -> C x y -> Set d}
          {x y u v p q}
        (f : {x : A} (y : B x) → (z : C x y) -> D x y z) → x === y → u === v → p === q -> f {x} u p === f {y} v q
cong3HetAiAeAe f refl refl refl = refl
-}








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

