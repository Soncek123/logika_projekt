module Project where

open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; [_])


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
    --     | ¬Var 𝑛f
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

-- 7. Define a type of conjunction normal form formulas called CNF

data Disjunct : Set where
  dlit : Literal → Disjunct
  _∨ᵈ_ : Literal → Disjunct → Disjunct

infixr 5 _∨ᵈ_

data CNF : Set where
  disj : Disjunct → CNF
  _∧ᶜ_ : Disjunct → CNF → CNF

infixr 6 _∧ᶜ_

-- 8. Define an evaluation function eval-cnf ∶ Assignment → CNF → Maybe Bool
-- assigning to each assignment of variables and conjunction normal from formula its truth value.

eval-disjunct : Assignment → Disjunct → Maybe Bool
eval-disjunct assn (dlit l) = eval-lit assn l
eval-disjunct assn (l ∨ᵈ d) =
  maybe-or (eval-lit assn l) (eval-disjunct assn d)

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf assn (disj d) = eval-disjunct assn d
eval-cnf assn (d ∧ᶜ c) =
  maybe-and (eval-disjunct assn d) (eval-cnf assn c)

  
-- 9. Write an SAT solver for CNF formulas. It should output either an as-
-- signment such that evaluating the formula at that assignment evaluates to true or that no such
-- assignment exists.
-- Note: a more complex implementation (e. g. DPLL) will be graded higher.

max : ℕ → ℕ → ℕ
max zero n = n
max (suc m) zero = suc m
max (suc m) (suc n) = suc (max m n)

max-lit : Literal → ℕ
max-lit (pos n) = n
max-lit (negLit n) = n

max-disjunct : Disjunct → ℕ
max-disjunct (dlit l) = max-lit l
max-disjunct (l ∨ᵈ d) = max (max-lit l) (max-disjunct d)

max-cnf : CNF → ℕ
max-cnf (disj d) = max-disjunct d
max-cnf (d ∧ᶜ c) = max (max-disjunct d) (max-cnf c)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

extend-with-var : ℕ → Assignment → List Assignment
extend-with-var n assn =
  (assn [ n ]≔ true) ∷ (assn [ n ]≔ false) ∷ []

extend-all : ℕ → List Assignment → List Assignment
extend-all n [] = []
extend-all n (assn ∷ assns) = extend-with-var n assn ++ extend-all n assns

assignments : ℕ → List Assignment
assignments zero = [] ∷ []
assignments (suc n) = extend-all n (assignments n)

find-sat : List Assignment → CNF → Maybe Assignment
find-sat [] c = nothing
find-sat (assn ∷ assns) c with eval-cnf assn c
... | just true = just assn
... | just false = find-sat assns c
... | nothing = find-sat assns c

sat-cnf : CNF → Maybe Assignment
sat-cnf c = find-sat (assignments (suc (max-cnf c))) c


-- 10. Show that the SAT solver you implemented is indeed correct, if that is not
-- obvious from the output type of the SAT solver.

record Satisfying (c : CNF) : Set where
  constructor satAssignment
  field
    assn : Assignment
    proof : eval-cnf assn c ≡ just true

find-sat-correct : (c : CNF) → List Assignment → Maybe (Satisfying c)
find-sat-correct c [] = nothing
find-sat-correct c (assn ∷ assns) with eval-cnf assn c in eq
... | just true = just (satAssignment assn eq)
... | just false = find-sat-correct c assns
... | nothing = find-sat-correct c assns

sat-cnf-correct : (c : CNF) → Maybe (Satisfying c)
sat-cnf-correct c =
  find-sat-correct c (assignments (suc (max-cnf c)))

-- 11. Write a function that converts an NNF formula to an equisatisfiable CNFformula.
-- Note: it is intended for you to attempt to implement the Tseytin transformation. A simpler
-- implementation will be accepted for partial credit.

disj-or-disj : Disjunct → Disjunct → Disjunct
disj-or-disj (dlit l) d₂ = l ∨ᵈ d₂
disj-or-disj (l ∨ᵈ d₁) d₂ = l ∨ᵈ disj-or-disj d₁ d₂

cnf-and : CNF → CNF → CNF
cnf-and (disj d) c₂ = d ∧ᶜ c₂
cnf-and (d ∧ᶜ c₁) c₂ = d ∧ᶜ cnf-and c₁ c₂

cnf-or-disj : CNF → Disjunct → CNF
cnf-or-disj (disj d₁) d₂ = disj (disj-or-disj d₁ d₂)
cnf-or-disj (d₁ ∧ᶜ c₁) d₂ =
  disj-or-disj d₁ d₂ ∧ᶜ cnf-or-disj c₁ d₂

cnf-or : CNF → CNF → CNF
cnf-or c₁ (disj d₂) = cnf-or-disj c₁ d₂
cnf-or c₁ (d₂ ∧ᶜ c₂) =
  cnf-and (cnf-or-disj c₁ d₂) (cnf-or c₁ c₂)

nnf-to-cnf : NNF → CNF
nnf-to-cnf (lit l) = disj (dlit l)
nnf-to-cnf (f ∧ⁿ g) = cnf-and (nnf-to-cnf f) (nnf-to-cnf g)
nnf-to-cnf (f ∨ⁿ g) = cnf-or (nnf-to-cnf f) (nnf-to-cnf g)

-- 12. To tie the bow on the whole thing, use the above to construct a SAT solver
-- for any formula.

sat-formula : Formula → Maybe Assignment
sat-formula f =
  sat-cnf (nnf-to-cnf (to-nnf f))

sat-formula-correct : (f : Formula) → Maybe (Satisfying (nnf-to-cnf (to-nnf f)))
sat-formula-correct f =
  sat-cnf-correct (nnf-to-cnf (to-nnf f))
