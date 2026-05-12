module Project where

open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)


-- 1. Define a type of formulas called Formula, with the following grammar:
        -- Formula → Var 𝑛
        -- | ¬Formula
        -- | Formula ∧ Formula
        -- | Formula ∨ Formula

data Formula : Set where
  var : ℕ → Formula
  neg : Formula → Formula
  _∧ᶠ_ : Formula → Formula → Formula
  _∨ᶠ_ : Formula → Formula → Formula

infixr 6 _∧ᶠ_
infixr 5 _∨ᶠ_

-- 2. Define a type of negation normal form formulas called NNF, with the following
-- grammar:
    --     Literal → Var 𝑛
    --     | ¬Var 𝑛
    --     NNF → Literal
    --     | NNF ∧ NNF
    --     | NNF ∨ NNF

data Literal : Set where
    pos : ℕ → Literal
    negLit : ℕ → Literal

data NNF : Set where
    lit : Literal → NNF
    _∧ⁿ_ : NNF → NNF → NNF
    _∨ⁿ_ : NNF → NNF → NNF

infixr 6 _∧ⁿ_
infixr 5 _∨ⁿ_

-- 3. Construct a function to-nnf of type Formula → NNF that converts a formula
-- to an equivalent formula in negation normal form.
-- Note: You may find a more suitable name for the functions.

mutual
  to-nnf : Formula → NNF
  to-nnf (var n) = lit (pos n)
  to-nnf (neg f) = to-nnf-neg f
  to-nnf (f ∧ᶠ g) = to-nnf f ∧ⁿ to-nnf g
  to-nnf (f ∨ᶠ g) = to-nnf f ∨ⁿ to-nnf g

  to-nnf-neg : Formula → NNF
  to-nnf-neg (var n) = lit (negLit n)
  to-nnf-neg (neg f) = to-nnf f
  to-nnf-neg (f ∧ᶠ g) = to-nnf-neg f ∨ⁿ to-nnf-neg g
  to-nnf-neg (f ∨ᶠ g) = to-nnf-neg f ∧ⁿ to-nnf-neg g

-- 4. 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (¬ A) → Dec A

record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)

open DecType
    
module AssocList (K : DecType) (V : Set) where

  Assoc : Set
  Assoc = List (carr K × V)

  infix 4 _∈_

  data _∈_ (k : carr K) : Assoc → Set where
    here  : {v : V} {kvs : Assoc}
          → k ∈ ((k , v) ∷ kvs)

    there : {k' : carr K} {v : V} {kvs : Assoc}
          → k ∈ kvs
          → k ∈ ((k' , v) ∷ kvs)

  lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
  lookup (here {v = v}) = v
  lookup (there p) = lookup p

  _∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? [] = no (λ ())
  k ∈? ((k' , v) ∷ kvs) with test-≡ K k k'
  ... | yes refl = yes here
  ... | no k≢k' with k ∈? kvs
  ...   | yes p = yes (there p)
  ...   | no k∉kvs =
    no (λ
      { here → k≢k' refl
      ; (there p) → k∉kvs p
      })

  _‼_ : Assoc → carr K → Maybe V
  kvs ‼ k with k ∈? kvs
  ... | yes p = just (lookup p)
  ... | no  _ = nothing

  _[_]≔_ : Assoc → carr K → V → Assoc
  [] [ k ]≔ v = (k , v) ∷ []
  ((k' , v') ∷ kvs) [ k ]≔ v with test-≡ K k k'
  ... | yes refl = (k , v) ∷ kvs
  ... | no _ = (k' , v') ∷ (kvs [ k ]≔ v)

𝒩 : DecType
𝒩 .carr = ℕ
𝒩 .test-≡ zero zero = yes refl
𝒩 .test-≡ zero (suc n) = no λ ()
𝒩 .test-≡ (suc m) zero = no λ ()
𝒩 .test-≡ (suc m) (suc n) with 𝒩 .test-≡ m n
... | yes refl = yes refl
... | no m≢n = no λ { refl → m≢n refl }

open AssocList 𝒩 Bool

Assignment : Set
Assignment = Assoc

-- 5. Define an evaluation function eval ∶ Assignment → Formula → Maybe Bool
-- assigning to each assignment of variables and formula its truth value.

maybe-not : Maybe Bool → Maybe Bool
maybe-not nothing = nothing
maybe-not (just b) = just (not b)

maybe-and : Maybe Bool → Maybe Bool → Maybe Bool
maybe-and nothing y = nothing
maybe-and x nothing = nothing
maybe-and (just true)  (just true)  = just true
maybe-and (just true)  (just false) = just false
maybe-and (just false) (just true)  = just false
maybe-and (just false) (just false) = just false

maybe-or : Maybe Bool → Maybe Bool → Maybe Bool
maybe-or nothing y = nothing
maybe-or x nothing = nothing
maybe-or (just true)  (just true)  = just true
maybe-or (just true)  (just false) = just true
maybe-or (just false) (just true)  = just true
maybe-or (just false) (just false) = just false

eval : Assignment → Formula → Maybe Bool
eval assn (var n) = assn ‼ n
eval assn (neg f) = maybe-not (eval assn f)
eval assn (f ∧ᶠ g) = maybe-and (eval assn f) (eval assn g)
eval assn (f ∨ᶠ g) = maybe-or (eval assn f) (eval assn g)

-- 6. Define an evaluation function eval-nnf ∶ Assignment → NNF → Maybe Bool
-- assigning to each assignment of variables and negation normal from formula its truth value.

eval-lit : Assignment → Literal → Maybe Bool
eval-lit assn (pos n) = assn ‼ n
eval-lit assn (negLit n) = maybe-not (assn ‼ n)

eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf assn (lit l) = eval-lit assn l
eval-nnf assn (f ∧ⁿ g) = maybe-and (eval-nnf assn f) (eval-nnf assn g)
eval-nnf assn (f ∨ⁿ g) = maybe-or (eval-nnf assn f) (eval-nnf assn g)