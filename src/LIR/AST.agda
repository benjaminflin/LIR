module LIR.AST where 

open import Data.Nat.Base
open import Data.Fin hiding (_+_; cast) renaming (_≟_ to _F≟_)
open import Data.List.Base 
open import Data.Bool.Base hiding (not)
open import Data.Product
open import Relation.Nullary
open import Data.Integer.Base hiding (_+_; suc)
open import Relation.Binary.PropositionalEquality

data BaseType : Set where
    int : BaseType
    -- float : (double : Bool) → BaseType
    unit : BaseType

data Type : Set where
    base-type : BaseType → Type
    pointer : Type → Type 
    function : List Type → Type → Type
    array : ℕ → Type → Type 
    struct : List Type → Type



data Var (m n : ℕ) : Set where
    global : Fin m → Var m n 
    local : Fin n → Var m n



_≟_ : ∀ {m n} (x y : Var m n) → Dec (x ≡ y) 
global x ≟ global y with (x F≟ y) 
... | yes refl = yes refl  
... | no contra = no (λ where refl → contra refl)
global x ≟ local y = no λ () 
local x ≟ global y = no λ ()
local x ≟ local y with (x F≟ y) 
... | yes refl = yes refl  
... | no contra = no (λ where refl → contra refl)

BlockRef : ℕ → Set
BlockRef n = Fin n

data Binop : Set where
    add subtract multiply divide : Binop 

data Unop : Set where
    negate not : Unop

data Offset : Set where
    field-offset array-offset : ℕ → Offset
    no-offset : Offset



data Const : Set where
    int : ℤ → Const
    unit : Const

type-of-const : Const → Type 
type-of-const (int x) = base-type int
type-of-const unit = base-type unit

data Expr (m n : ℕ) : Set where
    var : Var m n → Expr m n  
    const : Const → Expr m n

data Instruction (m n : ℕ) : Set where
    binop : Expr m n → Binop → Expr m n → Instruction m n
    unop : Unop → Expr m n → Instruction m n
    store : Expr m n → Var m n → Instruction m n
    alloca : Type → Instruction m n
    load : Var m n → Instruction m n
    offset : Var m n → Offset → Instruction m n
    call : Var m n → List (Var m n) → Instruction m n 
    cast : Expr m n → Type → Instruction m n

data Terminator (m n p : ℕ) : Set where 
    br : BlockRef p → Terminator m n p
    condbr : Var m n → BlockRef p → Terminator m n p
    ret : Var m n → Terminator m n p

data IndexedVec (F : ℕ → Set) : ℕ → Set where  
    [] : IndexedVec F 0
    _∷_ : ∀ {n} → F n → IndexedVec F n → IndexedVec F (suc n) 

record BasicBlock (global-size : ℕ) (prev-inst-size : ℕ) (block-size : ℕ) : Set where
    field
        size : ℕ
        instructions : IndexedVec (Instruction global-size) (prev-inst-size + size)
        terminator : Terminator global-size (prev-inst-size + size) block-size

record Function (global-size : ℕ) : Set where
    field
        params : List Type  
        block-size : ℕ
        basic-blocks : IndexedVec (BasicBlock global-size (length params)) block-size

record Global (global-size : ℕ) : Set where  
    field
        type : Type  
        init : Const

record Module : Set where
    field
        num-globals : ℕ
        functions : List (Function num-globals) 
        globals : List (Global num-globals) 
        global-count : length functions + length globals ≡ num-globals