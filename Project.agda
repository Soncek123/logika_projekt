module code where

open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; [_])

--------------------------------------------------------------------------------
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

------------------------------------------------------------------------------------
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
---------------------------------------------------------------------------------------
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

----------------------------------------------------------------------
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

-------------------------------------------------------------------------------
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

--------------------------------------------------------------------------------------
-- 6. Define an evaluation function eval-nnf ∶ Assignment → NNF → Maybe Bool
-- assigning to each assignment of variables and negation normal from formula its truth value.

eval-lit : Assignment → Literal → Maybe Bool
eval-lit assn (pos n) = assn ‼ n
eval-lit assn (negLit n) = maybe-not (assn ‼ n)

eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf assn (lit l) = eval-lit assn l
eval-nnf assn (f ∧ⁿ g) = maybe-and (eval-nnf assn f) (eval-nnf assn g)
eval-nnf assn (f ∨ⁿ g) = maybe-or (eval-nnf assn f) (eval-nnf assn g)


-----------------------------------------------------------------------------
-- 7. Define a type of conjunction normal form formulas called CNF

data Disjunct : Set where
  dlit : Literal → Disjunct
  _∨ᵈ_ : Literal → Disjunct → Disjunct

infixr 5 _∨ᵈ_

data CNF : Set where
  disj : Disjunct → CNF
  _∧ᶜ_ : Disjunct → CNF → CNF

infixr 6 _∧ᶜ_


----------------------------------------------------------------------------------------
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


-------------------------------------------------------------
--9.Write an SAT solver for CNF formulas. It should output either an assignment such that evaluating the 
--formula at that assignment evaluates to true or that no such assignment exists.
--Note: a more complex implementation (e. g. DPLL) will be graded higher.

Clause : Set
Clause = List Literal

DPLLFormula : Set
DPLLFormula = List Clause


disjunct-to-clause : Disjunct → Clause
disjunct-to-clause (dlit l) = l ∷ []
disjunct-to-clause (l ∨ᵈ d) = l ∷ disjunct-to-clause d

cnf-to-formula : CNF → DPLLFormula
cnf-to-formula (disj d) = disjunct-to-clause d ∷ []
cnf-to-formula (d ∧ᶜ c) = disjunct-to-clause d ∷ cnf-to-formula c


nat-eq-bool : ℕ → ℕ → Bool
nat-eq-bool m n with 𝒩 .test-≡ m n
... | yes _ = true
... | no _ = false

lit-eq : Literal → Literal → Bool
lit-eq (pos m) (pos n) = nat-eq-bool m n
lit-eq (negLit m) (negLit n) = nat-eq-bool m n
lit-eq (pos m) (negLit n) = false
lit-eq (negLit m) (pos n) = false



opposite : Literal → Literal
opposite (pos n) = negLit n
opposite (negLit n) = pos n



contains-lit : Literal → Clause → Bool
contains-lit l [] = false
contains-lit l (x ∷ xs) with lit-eq l x
... | true = true
... | false = contains-lit l xs



remove-lit : Literal → Clause → Clause
remove-lit l [] = []
remove-lit l (x ∷ xs) with lit-eq l x
... | true = remove-lit l xs
... | false = x ∷ remove-lit l xs



simplify-clause : Literal → Clause → Maybe Clause
simplify-clause l c with contains-lit l c
... | true = nothing
... | false = just (remove-lit (opposite l) c)



simplify-formula : Literal → DPLLFormula → DPLLFormula
simplify-formula l [] = []
simplify-formula l (c ∷ cs) with simplify-clause l c
... | nothing = simplify-formula l cs
... | just c' = c' ∷ simplify-formula l cs



assign-lit : Assignment → Literal → Assignment
assign-lit assn (pos n) = assn [ n ]≔ true
assign-lit assn (negLit n) = assn [ n ]≔ false



find-unit : DPLLFormula → Maybe Literal
find-unit [] = nothing
find-unit ([] ∷ cs) = find-unit cs
find-unit ((l ∷ []) ∷ cs) = just l
find-unit ((l ∷ x ∷ xs) ∷ cs) = find-unit cs



has-empty-clause : DPLLFormula → Bool
has-empty-clause [] = false
has-empty-clause ([] ∷ cs) = true
has-empty-clause ((x ∷ xs) ∷ cs) = has-empty-clause cs



formula-empty : DPLLFormula → Bool
formula-empty [] = true
formula-empty (c ∷ cs) = false



pick-literal : DPLLFormula → Maybe Literal
pick-literal [] = nothing
pick-literal ([] ∷ cs) = pick-literal cs
pick-literal ((l ∷ xs) ∷ cs) = just l



_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

clause-size : Clause → ℕ
clause-size [] = zero
clause-size (l ∷ ls) = suc (clause-size ls)

formula-size : DPLLFormula → ℕ
formula-size [] = zero
formula-size (c ∷ cs) = clause-size c + formula-size cs



dpll : ℕ → DPLLFormula → Assignment → Maybe Assignment
dpll zero f assn = nothing
dpll (suc fuel) f assn with find-unit f
... | just l =
  dpll fuel (simplify-formula l f) (assign-lit assn l)

... | nothing with has-empty-clause f
...   | true = nothing

...   | false with formula-empty f
...     | true = just assn

...     | false with pick-literal f
...       | nothing = just assn

...       | just l with dpll fuel (simplify-formula l f) (assign-lit assn l)
...         | just assn' = just assn'
...         | nothing =
  dpll fuel
       (simplify-formula (opposite l) f)
       (assign-lit assn (opposite l))



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

assign-default : Assignment → ℕ → Assignment
assign-default assn n with assn ‼ n
... | just b = assn
... | nothing = assn [ n ]≔ false

complete-up-to : ℕ → Assignment → Assignment
complete-up-to zero assn = assign-default assn zero
complete-up-to (suc n) assn =
  assign-default (complete-up-to n assn) (suc n)

sat-cnf : CNF → Maybe Assignment
sat-cnf c with dpll (suc (formula-size (cnf-to-formula c)))
                   (cnf-to-formula c)
                   []
... | nothing = nothing
... | just assn = just (complete-up-to (max-cnf c) assn)


is-sat : CNF → Bool
is-sat c with sat-cnf c
... | nothing = false
... | just assn = true


-------------------------------------------------------------------------------
-- 10. Show that the SAT solver you implemented is indeed correct, if that is not
--obvious from the output type of the SAT solver.


record Satisfying (c : CNF) : Set where
  constructor satAssignment
  field
    assn  : Assignment
    proof : eval-cnf assn c ≡ just true

certify-sat : (c : CNF) → (assn : Assignment) →
              (r : Maybe Bool) →
              eval-cnf assn c ≡ r →
              Maybe (Satisfying c)
certify-sat c assn (just true) eq = just (satAssignment assn eq)
certify-sat c assn (just false) eq = nothing
certify-sat c assn nothing eq = nothing

sat-cnf-correct : (c : CNF) → Maybe (Satisfying c)
sat-cnf-correct c with sat-cnf c
... | nothing = nothing
... | just assn = certify-sat c assn (eval-cnf assn c) refl



-- If sat-cnf-correct returns just, correctness is immediate from the output
-- type, because the returned proof has type:
--
--   eval-cnf assn c ≡ just true
--
-- The nothing case is not fully certified here. Proving that nothing means
-- unsatisfiable would require proving completeness of the DPLL procedure and
-- that the chosen fuel is sufficient.

---------------------------------------------------------------------------------------
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

-----------------------------------------------------------------------------------
-- 12. To tie the bow on the whole thing, use the above to construct a SAT solver
-- for any formula.

sat-formula : Formula → Maybe Assignment
sat-formula f =
  sat-cnf (nnf-to-cnf (to-nnf f))
