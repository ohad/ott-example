{-# OPTIONS --rewriting --prop #-}

module ott where 

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  A B C       : Set 
  P Q         : A → Set 
  x y z       : A
  f g h       : (x : A) → P x
  b b1 b2 b3  : Bool
  j k m n     : Nat
  xs ys zs    : List A

-- Declare some propositions

record ⊤ : Prop where constructor tt

data   ⊥ : Prop where

record _∧_ (X : Prop) (Y : Prop) : Prop where
  constructor _,_
  field
    fst : X
    snd : Y
open _∧_

-- Let's postulate the heterogenous OTT equality. 

infix 6 _==_

postulate
  _==_  : {A : Set}  {B : Set}  → A → B → Prop  -- term equality
  _===_ : Set → Set → Prop₁                     -- type equality

infix 6 _===_

-- if A : Prop, and a b : A then a ≡ b 

HEq = _==_
syntax HEq {A = A} {B = B} x y = A ∋ x == y ∈ B


postulate
    _·_ : {A : Set} {B : Set} {C : Set} {a : A} {b : B} {c : C} 
          → (A ∋ a == b ∈ B) 
          → (B ∋ b == c ∈ C) 
          → (A ∋ a == c ∈ C) 

    sym : {A : Set} {B : Set} {a : A} {b : B}
          → (A ∋ a == b ∈ B) 
          → (B ∋ b == a ∈ A) 

    refl-set : (S : Set) → (S === S)

-- Support for Booleans

postulate
  refl-Bool   : (Bool === Bool)

  refl-true   : (true  == true)  ≡ ⊤
  refl-false  : (false == false) ≡ ⊤
  conflict-tf : (true  == false) ≡ ⊥
  conflict-ft : (false == true)  ≡ ⊥

{-# REWRITE refl-true 
            refl-false
            conflict-tf 
            conflict-ft #-}

-- Support for dependent functions 

postulate
  -- We postulate that two codes for functions Πx:A.P(x) and Πy:B.Q(y)
  -- are equal when A == B and for all equal x and y, P(x) equals Q(y)
  -- 
  cong-Π : (B === A) → 
           ((x : A)(y : B) → y == x → P x === Q y)
           → 
           ((x : A) → P x) === ((y : B) → Q y)

  -- injectivity of pi-type constructor
  out-Π-1 : ((x : A) → P x) === ((y : B) → Q y) → (B === A)
  out-Π-2 : ((x : A) → P x) === ((y : B) → Q y) → ((x : A)(y : B) → y == x → P x === Q y)

-- Two functions f and g are equal when they are pointwise equal

  ext-λ : {A : Set} {B : Set}
    → {P : A → Set} {Q : B → Set}
    → (f : (x : A) → P x) (g : (y : B) → Q y)
    → ((x : A) (y : B) (x==y : x == y) → f x == g y)
    → (f == g)
    
infix 10 _[_⟩ _||_

postulate
  _[_⟩    : A → (A === B) → B      -- Coercion
  _||_    : (x : A) (Q : A === B)
          → A ∋ x == x [ Q ⟩ ∈ B   -- Coherence


postulate
  coerce-Bool : (pf : Bool === Bool)
              → b [ pf ⟩ ≡ b
  coerce-Π : 
      {A : Set} {B : Set}
      {P : A → Set} {Q : B → Set}
    → (E : ((x : A) → P x) === ((y : B) → Q y))
    → (f : (x : A) → P x) 
    → let B===A : B === A 
          B===A = out-Π-1 E 
          P===Q : (x : A)(y : B) → y == x → P x === Q y
          P===Q = out-Π-2 E 
          g : (y : B) → Q y 
          g = λ y → let x : A 
                        x = y [ B===A ⟩ 
                        v : P x 
                        v = f x
                        q : y == x
                        q = y || B===A 
                        R : P x === Q y 
                        R = P===Q x y q
                     in v [ R ⟩ 
      in 
      (f [ E ⟩ ≡ g)
  
{-# REWRITE coerce-Bool 
            coerce-Π
#-}

postulate
  cong-set : {S : Set} → (T : (x : S) → Set) → {x y : S} → (S ∋ x == y ∈ S) → T x === T y
  Refl : {S : Set} {s : S} → S ∋ s == s ∈ S
  
replace : {S : Set} (T : (x : S) → Set) → {x y : S} → (S ∋ x == y ∈ S) → T x → T y
replace T x==y tx = tx [ cong-set T x==y ⟩

postulate
  Quote : Prop → Set
  MkQuote : {P : Prop} → P → Quote P
  Unquote : {P : Prop} → Quote P → P

cong : {S : Set} {T : S → Set} → (f : (x : S) → T x) → {x y : S} → (S ∋ x == y ∈ S)
    → T x ∋ f x == f y ∈ T y
cong {S} {T} f {x} {y} x==y =
  Unquote (replace (λ z → Quote (T x ∋ f x == f z ∈ T z)) x==y (MkQuote (Refl {s = f x})))

infix 9 _/_

postulate
  _/_ : (A : Set) → (R : A → A → Set) → Set 

  [_] : {A : Set} {R : A → A → Set} → A → A / R 



  -- let [x] = v in k because pf 

  quotient-elim : {A : Set} 
                  {B : Set} 
                  {R : A → A → Set} 
                  → (v : A / R)
                  → (k : (x : A) → B)
                  → (pf : ∀ (a a' : A) → R a a' → B ∋ k a == k a' ∈ B)
                  → B 

 -- let [x] = [v] in k(x) because pf ≡ k(v)
 
  quotient-reduce : {A : Set}
                    {B : Set}
                    {R : A → A → Set}
                    → (v : A)
                    → (k : A → B)
                    → (pf : ∀ (a a' : A) → R a a' → B ∋ k a == k a' ∈ B)
                    → quotient-elim [ v ] k pf ≡ k v 

  quotient-== : {A : Set}
                {R : A → A → Set}
                → (x y : A)
                → (R x y)
                → (A / R) ∋ [ x ] == [ y ] ∈ (A / R)
 
  quotient-=== : {A : Set} {R : A → A → Set}
                 {B : Set} {S : B → B → Set}
                 → (A === B)
                 → ((a a' : A) (b b' : B) → (A ∋ a == b ∈ B) → (A ∋ a' == b' ∈ B) → R a a' === S b b')
                 → A / R === B / S 

  out-quotient-1 : {A : Set} {R : A → A → Set} 
                   {B : Set} {S : B → B → Set} →
                   (A / R === B / S) → (A === B)

  out-quotient-2 : {A : Set} {R : A → A → Set} →
                   {B : Set} {S : B → B → Set} →
                   (A / R === B / S) → 
                   ((a a' : A) (b b' : B) → (A ∋ a  == b ∈ B) → (A ∋ a' == b' ∈ B) → R a a' === S b b')

  coerce-quotient : {A : Set} {R : A → A → Set} 
                    {B : Set} {S : B → B → Set} →
                    (v : A / R) → 
                    (E : A / R === B / S) → 
                    v [ E ⟩ ≡ let A===B = out-quotient-1 E in 
                              quotient-elim v (λ a → [ a [ A===B ⟩ ]) 
                                (λ a a' aRa' → let b  = a  [ A===B ⟩ 
                                                   b' = a' [ A===B ⟩ 
                                                   a=b = a || A===B 
                                                   a'=b' = a' || A===B 
                                                   aRa'==bSb' = out-quotient-2 E a a' b b' a=b a'=b'
                                                   bSb' = aRa' [ aRa'==bSb' ⟩
                                                in 
                                                quotient-== b b' bSb')


{- REWRITE quotient-reduce  
           coerce-quotient -}


-- From Agda stdlib

infix  4 _IsRelatedTo_
infix  3 _∎
infixr 2 step-∼
infix  1 begin_

------------------------------------------------------------------------
-- Definition of "related to"

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _IsRelatedTo_ {A B : Set} (x : A) (y : B) : Set where
  relTo : (x∼y : A ∋ x == y ∈ B) → x IsRelatedTo y


{- We can encode pairs as dependent products, but then we'll lose out
on pattern matching -}

record Pair (A B : Set) : Set where
  constructor ⟪_,_⟫
  field
    fst : A
    snd : B 

open Pair
module _ { A B A' B' : Set} where
  record PairEq (p : Pair A B) (q : Pair A' B') : Set where
    constructor MkPairEq
    field
      fst-== : fst p == fst q
      snd-== : snd p == snd q

  postulate
    Pair-=== : A === A'
           →  B === B'
           → Pair A B === Pair A' B'
           
    out-pair-fst : Pair A B === Pair A' B'
                → A === A'

    out-pair-snd : Pair A B === Pair A' B'
                → B === B'

    Pair-== :   (AB==A'B' : Pair A B === Pair A' B')
             → (p : Pair A  B )
             → (p' : Pair A' B')
             → PairEq p p'
             → Pair A B ∋ p == p' ∈ Pair A' B'

    coerce-pair : (E : Pair A B === Pair A' B')
               → (p : Pair A B)
               → p [ E ⟩ ≡ ⟪ fst p [ out-pair-fst E ⟩
                            , snd p [ out-pair-snd E ⟩
                            ⟫

{- REWRITE coerce-pair -}


------------------------------------------------------------------------
-- Reasoning combinators

-- Note that the arguments to the `step`s are not provided in their
-- "natural" order and syntax declarations are later used to re-order
-- them. This is because the `step` ordering allows the type-checker to
-- better infer the middle argument `y` from the `_IsRelatedTo_`
-- argument (see issue 622).
--
-- This has two practical benefits. First it speeds up type-checking by
-- approximately a factor of 5. Secondly it allows the combinators to be
-- used with macros that use reflection, e.g. `Tactic.RingSolver`, where
-- they need to be able to extract `y` using reflection.

-- Beginning of a proof


begin_ : ∀ {A B x y} → x IsRelatedTo y → A ∋ x == y ∈ B
begin relTo x∼y = x∼y

-- Standard step with the relation

step-∼ : ∀ {A B C} → (x : A) → {y : B} { z : C} → y IsRelatedTo z → _ ∋ x == y ∈ _ → x IsRelatedTo z
step-∼ {A} x (relTo y∼z) x∼y = relTo (_·_ {A = A} x∼y y∼z) --(x∼y · y∼z)

_∎ : ∀ {A}  → (x : A) → x IsRelatedTo x
x ∎ = relTo (Refl {s = x})

-- Syntax declarations

syntax step-∼  x y∼z x∼y = x ==⟨  x∼y ⟩ y∼z


record LocallySmall : Set₂ where
  constructor MkLSCat
  field
    Obj : Set₁
    Hom : Obj -> Obj -> Set

    id : {A : Obj} → Hom A A
    _∘_ : {A B C : Obj} -> Hom B C -> Hom A B -> Hom A C

    id-lft : {A B : Obj} → (f : Hom A B) → Hom A B ∋ (id ∘ f)  == f ∈ Hom A B
    id-rgt : {A B : Obj} → (f : Hom A B) → Hom A B ∋ (f ∘ id)  == f ∈ Hom A B
    assoc  : {A B C D : Obj} → (h : Hom C D) → (g : Hom B C) → (f : Hom A B)
           → Hom A D ∋ h ∘ (g ∘ f) == (h ∘ g) ∘ f ∈ Hom A D

open LocallySmall using (Obj)

Hom[_,_] : {C : LocallySmall} -> (A B : LocallySmall.Obj C) -> Set
Hom[_,_] {C} A B = LocallySmall.Hom C A B

------------ Observational Equality for LocallySmall categories ----
-- A bespoke type system would implement this generically for
-- records and datatypes
-- With the current approach we'll need to encode records and datatypes in
-- order to do this.

-- TODO: Implement level polymorphism to do this properly.
    

-----------------------------------------------------



record Cat : Set₁ where
  constructor MkCat
  field
    Obj : Set
    Hom : Obj -> Obj -> Set

    id : {A : Obj} → Hom A A
    _∘_ : {A B C : Obj} -> Hom B C -> Hom A B -> Hom A C

    id-lft : {A B : Obj} → (f : Hom A B) → Hom A B ∋ (id ∘ f)  == f ∈ Hom A B
    id-rgt : {A B : Obj} → (f : Hom A B) → Hom A B ∋ (f ∘ id)  == f ∈ Hom A B
    assoc  : {A B C D : Obj} → (h : Hom C D) → (g : Hom B C) → (f : Hom A B)
           → Hom A D ∋ h ∘ (g ∘ f) == (h ∘ g) ∘ f ∈ Hom A D

open Cat using (Obj)

Hom⟨_,_⟩ : {C : Cat} -> (A B : Obj C) -> Set
Hom⟨_,_⟩ {C} A B = Cat.Hom C A B

------------ Observational Equality for Cat (small categories) ----

module _ (CC₁ CC₂ : Cat) where
  open Cat CC₁ renaming (Obj to Obj₁ ; Hom to Hom₁ ; id to id₁ ; _∘_ to _∘₁_ )
  open Cat CC₂ renaming (Obj to Obj₂ ; Hom to Hom₂ ; id to id₂ ; _∘_ to _∘₂_ )
  record CatEq  : Set₂ where
    constructor MkCatEq
    field
      obj-=== : Obj₁ === Obj₂
      hom-=== : (A₁ B₁ : Obj₁) → (A₂ B₂ : Obj₂)
              → Hom₁ A₁ B₁ === Hom₂ A₂ B₂

      id-== : (A₁ : Obj₁) → (A₂ : Obj₂) → (Obj₁ ∋ A₁ == A₂ ∈ Obj₂)
           → Hom₁ A₁ A₁ ∋ id₁ == id₂ ∈ Hom₂ A₂ A₂
           
      ∘-== : {A₁ B₁ C₁ : Obj₁} → (g₁ : Hom₁ B₁ C₁) → (f₁ : Hom₁ A₁ B₁)
          → {A₂ B₂ C₂ : Obj₂} → (g₂ : Hom₂ B₂ C₂) → (f₂ : Hom₂ A₂ B₂)
          → Hom₁ A₁ C₁ ∋ g₁ ∘₁ f₁ == g₂ ∘₂ f₂ ∈ Hom₂ A₂ C₂

{- Need level polymorphism to get equality of categories to work 
postulate

  ext-Cat : {CC₁ CC₂ : Cat} → CatEq CC₁ CC₂ → Cat ∋ CC₁ == CC₂ ∈ Cat
-}

-- Structure
module _ where
  open LocallySmall

  SetFun : LocallySmall
  Obj SetFun = Set
  Hom SetFun X Y =  X → Y
  id  SetFun = λ x → x
  _∘_ SetFun g f = λ x → g (f x)
  -- Properties
  id-lft SetFun f = Refl {s = f}
  id-rgt SetFun f = Refl {s = f}
  assoc  SetFun h g f = Refl {s = λ x → h (g (f x))}

module _ where
  open Cat
  _ᵒᵖ : Cat → Cat
  -- Structure
  Obj (C ᵒᵖ) = Obj C
  Hom (C ᵒᵖ) X Y = Hom C Y X
  id  (C ᵒᵖ) = id C
  _∘_ (C ᵒᵖ) g f = _∘_ C f g   -- Yuck!
  -- Properties
  id-lft (C ᵒᵖ) = id-rgt C
  id-rgt (C ᵒᵖ) = id-lft C
  assoc (C ᵒᵖ) {A} {_} {_} {D} h g f = sym {A = Hom C D A } 
                                          (assoc C f g h)

  _×_ : Cat → Cat → Cat
  -- Structure
  Obj (C₁ × C₂) = Pair (Obj C₁) (Obj C₂)
  Hom (C₁ × C₂) ⟪ A₁ , A₂ ⟫ ⟪ B₁ , B₂ ⟫ = Pair (Hom C₁ A₁ B₁) (Hom C₂ A₂ B₂)
  id  (C₁ × C₂) = ⟪ id C₁ , id C₂ ⟫
  ((C₁ × C₂) ∘ ⟪ g₁ , g₂ ⟫) ⟪ f₁ , f₂ ⟫ = ⟪ g₁ ∘₁ f₁  , g₂ ∘₂ f₂ ⟫
    where open Cat C₁ hiding (Obj) renaming (_∘_ to _∘₁_)
          open Cat C₂ hiding (Obj) renaming (_∘_ to _∘₂_)
  -- Property
  id-lft (C₁ × C₂) ⟪ f₁ , f₂ ⟫ = Pair-== (refl-set _) _ _
                                   (MkPairEq (Cat.id-lft C₁ _)
                                             (Cat.id-lft C₂ _))
  id-rgt (C₁ × C₂) ⟪ f₁ , f₂ ⟫ = Pair-== (refl-set _) _ _
                                   (MkPairEq (Cat.id-rgt C₁ _)
                                             (Cat.id-rgt C₂ _))
  assoc (C₁ × C₂) ⟪ h₁ , h₂ ⟫ ⟪ g₁ , g₂ ⟫ ⟪ f₁ , f₂ ⟫ =
    Pair-== (refl-set _) _ _ (MkPairEq (Cat.assoc C₁ _ _ _)
                                       (Cat.assoc C₂ _ _ _))


module _ (C : Cat) (D : LocallySmall) where
  open Cat C hiding (Obj)
  open LocallySmall D hiding (Obj)
                      renaming (Hom to Hom' ;
                                id  to id'  ;
                                _∘_ to _∘'_  )

  record Functor : Set₁ where
    constructor MkFunctor
    field
        _∗_ : Cat.Obj C → LocallySmall.Obj D
        _⋆_ : {A B : Cat.Obj C} → Cat.Hom C A B → LocallySmall.Hom D ( (_∗_) A ) ((_∗_) B )
    
        id-preservation : (A : Obj C) → _⋆_ (id {A}) == id' {_∗_ A}
        ∘-preservation  : {A B C' : Obj C} → (g : Hom B C') → (f : Hom A B ) →
                         (_⋆_) (g ∘ f) == ((_⋆_) g) ∘' ((_⋆_) f)

  {- Need level polymorphism for this too 
  open Functor
  module _ (F₁ F₂ : Functor) where
    record FunctorEq  : Set where
      constructor MkFunctorEq
      field
        ∗-=== : (_∗_ F₁) == (_∗_ F₂)
        ⋆-== : _ ∋ (_⋆_ F₁) == (_⋆_ F₂) ∈ _
  -}


module _ {C : Cat} {D : LocallySmall} (F G : Functor C D)  where
  open Cat C hiding (Obj)
  open LocallySmall D hiding (Obj) renaming (_∘_ to _∘'_)
  open Functor
  
  record NatTrans : Set where
    constructor MkNatTrans
    field
      _^_ : (A : Cat.Obj C) → LocallySmall.Hom D (F ∗ A) (G ∗ A)
  
      naturality : {A B : Cat.Obj C} → (f : Cat.Hom C A B) →
        (_^_ B) ∘' (F ⋆ f)  == _∘'_ (G ⋆ f) (_^_ A)

module _ {C : Cat} {D : LocallySmall} {F G : Functor C D} where
  open NatTrans 
  record NatTransEq (α β : NatTrans F G) : Set where
    constructor MkNatTransEq
    field
      ^-== : (_^_ α) == (_^_ β)

  postulate
    NatTrans-== : {α β : NatTrans F G} → NatTransEq α β → α == β

  {- Since we're not introducing === between NatTrans (we don't have
  == between functors!), that's it for now -}



-- TODO: do this for arbitrary locally small cats
module _ (C : Cat) (D : LocallySmall) where
  open Cat C hiding (Obj ; _∘_; Hom)
  open LocallySmall renaming (_∘_ to _∘'_)
  open Functor
  open NatTrans
  Fun : LocallySmall
  -- Structure
  Obj Fun = Functor C D
  Hom Fun F G = NatTrans F G
  _^_ (id Fun) _ = id D
  naturality (id Fun  {F}) {A} {B} f = begin
                               (id D) ∘ (F ⋆ f)
                               ==⟨ id-lft D (F ⋆ f) ⟩
                               F ⋆ f
                               ==⟨ sym {A = Hom D (F ∗ A)  (F ∗ B)} (id-rgt D (F ⋆ f)) ⟩
                               (F ⋆ f) ∘ (id D)
                               ∎ where open LocallySmall D using (_∘_; Hom)
  _^_        (_∘'_ Fun β α) A = LocallySmall._∘_ D (β ^ A) (α ^ A)  
  naturality (_∘'_ Fun {F} {G} {H} β α) {A} {B} f = 
               begin
               ((β ^ B) ∘ (α ^ B)) ∘ (F ⋆ f)
               ==⟨ sym {A = Hom D (F ∗ A) (H ∗ B)} (assoc D (β ^ B) (α ^ B) (F ⋆ f) ) ⟩
               (β ^ B) ∘ ((α ^ B) ∘ (F ⋆ f))
               ==⟨ cong ((β ^ B) ∘_) (naturality α f) ⟩  
               (β ^ B) ∘ ((G ⋆ f) ∘ (α ^ A) )
               ==⟨ assoc D (β ^ B) (G ⋆ f)  _ ⟩               
               ((β ^ B) ∘ (G ⋆ f)) ∘ (α ^ A)
               ==⟨ cong (λ u → u ∘ (α ^ A) ) (naturality β f) ⟩
               ((H ⋆ f) ∘ (β ^ A)) ∘ (α ^ A)
               ==⟨ sym {A = Hom D (F ∗ A) (H ∗ B)}
                       (assoc D (H ⋆ f) (β ^ A) (α ^ A))  ⟩
               ((H ⋆ f) ∘ ((β ^ A) ∘ (α ^ A)))
               ∎
    where open LocallySmall D using (_∘_ ; Hom)

  -- Property
  id-lft Fun  α = NatTrans-==
                 (MkNatTransEq
                   (ext-λ (λ A →
                     (id D) ∘ (α ^ A))
                     (_^_ α)
                     λ A A' A==A' →
                       begin
                       (id D) ∘ (α ^ A)
                       ==⟨ id-lft D (α ^ A) ⟩
                       (α ^ A)
                       ==⟨ cong (_^_ α) A==A' ⟩
                       α ^ A'
                       ∎
                  )) where open LocallySmall D using (_∘_ ; Hom)
  id-rgt Fun  α = NatTrans-==
                 (MkNatTransEq
                  (ext-λ
                    (λ A → (α ^ A) ∘ (id D))
                    (_^_ α)
                    λ A A' A==A' →
                    begin
                    (α ^ A) ∘ (id D)
                    ==⟨ id-rgt D (α ^ A) ⟩
                    α ^ A
                    ==⟨  cong (_^_ α) A==A' ⟩
                    α ^ A'
                    ∎
                 )) where open LocallySmall D using (_∘_ ; Hom)
  assoc  Fun  γ β α = NatTrans-==
                     (MkNatTransEq
                      (ext-λ
                        (λ A → (γ ^ A) ∘ ((β ^ A) ∘ (α ^ A)))
                        (λ A →((γ ^ A) ∘ ( β ^ A))∘ (α ^ A) )
                        λ A A' A==A' →
                        begin
                         (γ ^ A) ∘ ((β ^ A) ∘ (α ^ A))
                        ==⟨ assoc D (γ ^ A) (β ^ A) (α ^ A) ⟩
                        ((γ ^ A) ∘ ( β ^ A)) ∘ (α ^ A)
                        ==⟨ cong (λ - → ((γ ^ -) ∘ ( β ^ -)) ∘ (α ^ -)) A==A' ⟩
                        ((γ ^ A') ∘ ( β ^ A')) ∘ (α ^ A')
                        ∎
                     )) where open LocallySmall D using (_∘_ ; Hom)



-- Coends

-- Cocompleteness of SetFun : ∫^ F : (C : Cat) → (F : Functor (C ᵒᵖ × C) Set) → Set
-- coend' C F = Sigma (c : C) F ∗ (c , c)
-- coend-∼ C F (c, x) (c', x') = (f : C ⟨ c , c' ⟩ , x = (F ⋆ f) x' )
-- ∫^ F = coend' C F / coend-∼
-- prove universal property of coend.

