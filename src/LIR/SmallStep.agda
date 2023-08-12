module LIR.SmallStep where

open import Data.List
open import Data.Product
import Data.Nat as Nat
open Nat 
import Data.Fin as Fin 
open Fin renaming (suc to fsuc)
open import Data.Bool
import Data.Maybe as Maybe
open Maybe
open import Data.Integer using (ℤ)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 
open import Function
open import Level renaming (zero to ℓ₀; suc to lsuc) 
open import Relation.Unary hiding (_∈_)
open import LIR.AST 


IsJust : ∀ {A : Set} → Maybe A → Set
IsJust m = ∃[ x ] m ≡ just x

Context : ℕ → ℕ → Set 
Context m n = Var m n → Type

private
    variable
        m n : ℕ 
        Γ : Context m n

_,⦂_ : Context m n → Type → Context m (suc n)
(Γ ,⦂ t) (global y) = Γ (global y)
(Γ ,⦂ t) (local zero) = t
(Γ ,⦂ t) (local (fsuc y)) = Γ (local y) 

_⦂_∈_ : Var m n → Type → Context m n → Set
x ⦂ t ∈ Γ = Γ x ≡ t  

weaken-var : Var m n → Var m (suc n) 
weaken-var (global x) = global x
weaken-var (local x) = local (fsuc x)

weaken-∈ : ∀ {x : Var m n} {s t : Type} → x ⦂ t ∈ Γ → (weaken-var x) ⦂ t ∈ (Γ ,⦂ s)
weaken-∈ {x = global x} refl = refl
weaken-∈ {x = local x} refl = refl

strengthen-∈-global : ∀ {x : Fin m} {s t : Type} → (global x) ⦂ t ∈ (Γ ,⦂ s) → (global x) ⦂ t ∈ Γ 
strengthen-∈-global refl = refl

strengthen-∈-local : ∀ {x : Fin n} {s t : Type} → (local (fsuc x)) ⦂ t ∈ (Γ ,⦂ s) → (local x) ⦂ t ∈ Γ 
strengthen-∈-local refl = refl




data BoundedOffset {m n} (x : Var m n) : Context m n → Set where
    no-offset-bdd : BoundedOffset x Γ
    field-offset-bdd : ∀ {fs} → (f : Fin (length fs)) → (∈Γ : x ⦂ (struct fs) ∈ Γ) → BoundedOffset x Γ
    array-offset-bdd : ∀ {n t} → (f : Fin n) → (∈Γ : x ⦂ (array n t) ∈ Γ) → BoundedOffset x Γ

data AddBounded {x : Var m n} {Γ : Context m n} : BoundedOffset x Γ → BoundedOffset x Γ → BoundedOffset x Γ → Set where
    add-field-offsets : ∀ {k₁ k₂ : ℕ} {fs : List Type} 
        (f₁ : Fin k₁) (f₂ : Fin k₂) (∈Γ : x ⦂ (struct fs) ∈ Γ) 
        (η₁ : Fin k₁ → Fin (length fs))
        (η₂ : Fin k₂ → Fin (length fs))
        (ϕ : Fin (toℕ f₁ Nat.+ k₂) → Fin (length fs)) →
        AddBounded (field-offset-bdd (η₁ f₁) ∈Γ) (field-offset-bdd (η₂ f₂) ∈Γ) (field-offset-bdd (ϕ (f₁ Fin.+ f₂)) ∈Γ)
    add-array-offsets : ∀ {k₁ k₂ n : ℕ} {t : Type} 
        (f₁ : Fin k₁) (f₂ : Fin k₂) (∈Γ : x ⦂ (array n t) ∈ Γ) 
        (η₁ : Fin k₁ → Fin n)
        (η₂ : Fin k₂ → Fin n) 
        (ϕ : Fin (toℕ f₁ Nat.+ k₂) → Fin n) → 
        AddBounded (array-offset-bdd (η₁ f₁) ∈Γ) (array-offset-bdd (η₂ f₂) ∈Γ) (array-offset-bdd (ϕ (f₁ Fin.+ f₂)) ∈Γ)
    add-no-offsetˡ : (b : BoundedOffset x Γ) → AddBounded no-offset-bdd b b
    add-no-offsetʳ : (b : BoundedOffset x Γ) → AddBounded b no-offset-bdd b 



toOffset : ∀ {x : Var m n} → BoundedOffset x Γ → Offset 
toOffset no-offset-bdd = no-offset
toOffset (field-offset-bdd f ∈Γ) = field-offset (toℕ f)
toOffset (array-offset-bdd f ∈Γ) = array-offset (toℕ f)

Address : ∀ m n → (Γ : Context m n) → Set 
Address m n Γ = Σ[ x ∈ Var m n ] (BoundedOffset x Γ)

type-at-address : Address m n Γ → Type
type-at-address {Γ = Γ} (v , _) = Γ v

toAddress : Var m n → Address m n Γ 
toAddress x = x , no-offset-bdd

_A≟_ : (x y : Address m n Γ) → Dec (x ≡ y) 
(x , off₁) A≟ (y , off₂) = {!   !}

data Value (m n : ℕ) : Context m n → Set where
    constv : Const → Value m n Γ
    pointer : Address m n Γ → Value m n Γ


Memory : ∀ m n (Γ : Context m n) → Set 
Memory m n Γ = Address m n Γ → Maybe (Value m n Γ)


type-of-value : Value m n Γ → Type
type-of-value (constv x) = type-of-const x
type-of-value (pointer α) = type-at-address α

strengthen-off-global : ∀ {t : Type} {x : Fin m} → BoundedOffset (global x) (Γ ,⦂ t) → BoundedOffset (global x) Γ
strengthen-off-global no-offset-bdd = no-offset-bdd
strengthen-off-global {Γ = Γ} {t = t} (field-offset-bdd f ∈Γ) = field-offset-bdd f (strengthen-∈-global {Γ = Γ} {s = t} ∈Γ)
strengthen-off-global {Γ = Γ} {t = t} (array-offset-bdd f ∈Γ) = array-offset-bdd f (strengthen-∈-global {Γ = Γ} {s = t} ∈Γ) 

strengthen-off-local : ∀ {t : Type} {x : Fin m} → BoundedOffset (local (fsuc x)) (Γ ,⦂ t) → BoundedOffset (local x) Γ
strengthen-off-local no-offset-bdd = no-offset-bdd
strengthen-off-local {Γ = Γ} {t = t} (field-offset-bdd f ∈Γ) = field-offset-bdd f (strengthen-∈-local {Γ = Γ} {s = t} ∈Γ)
strengthen-off-local {Γ = Γ} {t = t} (array-offset-bdd f ∈Γ) = array-offset-bdd f (strengthen-∈-local {Γ = Γ} {s = t} ∈Γ) 

weaken-off : ∀ {t : Type} {x : Var m n} → BoundedOffset x Γ → BoundedOffset (weaken-var x) (Γ ,⦂ t)
weaken-off no-offset-bdd = no-offset-bdd
weaken-off {Γ = Γ} (field-offset-bdd f ∈Γ) = field-offset-bdd f (weaken-∈ {Γ = Γ} ∈Γ)
weaken-off {Γ = Γ} (array-offset-bdd f ∈Γ) = array-offset-bdd f (weaken-∈ {Γ = Γ} ∈Γ)

↑₁ : ∀ {m n Γ} {t : Type} → Value m n Γ → Value m (suc n) (Γ ,⦂ t)
↑₁ (constv x) = constv x
↑₁ (pointer (global x , o)) = pointer (global x , weaken-off o)
↑₁ (pointer (local x , o)) = pointer (local (fsuc x) , weaken-off o )

new : (t : Type) → Memory m n Γ → Memory m (suc n) (Γ ,⦂ t)
new _ ρ (global x , o) = Maybe.map ↑₁ (ρ (global x , strengthen-off-global o))
new _ ρ (local zero , o) = nothing 
new _ ρ (local (fsuc x) , o) = Maybe.map ↑₁ (ρ (local x , strengthen-off-local o)) 

new-init : (v : Value m n Γ) → (ρ : Memory m n Γ) → Memory m (suc n) (Γ ,⦂ type-of-value v)
new-init _ ρ (global x , o) = Maybe.map ↑₁ (ρ (global x , strengthen-off-global o))
new-init v ρ (local zero , no-offset-bdd) = just (↑₁ v)
new-init v ρ (local zero , o) = nothing
new-init _ ρ (local (fsuc x) , o) = Maybe.map ↑₁ (ρ (local x , strengthen-off-local o)) 

set : Memory m n Γ → Address m n Γ → Value m n Γ → Memory m n Γ
set ρ x v y = if does (x A≟ y) then just v else ρ x

Env : ∀ m → Set
Env m = ∃[ n ] ∃[ Γ ] Memory m n Γ

⟨_⟩ : Memory m n Γ → Env m 
⟨ ρ ⟩ = -, -, ρ 

eval : Memory m n Γ → Expr m n → Maybe (Value m n Γ)
eval ρ (var x) = ρ (toAddress x) 
eval ρ (Expr.const x) = just (constv x)
Init : Memory m n Γ → Expr m n → Set
Init ρ e = IsJust (eval ρ e)  

private variable 
    ρ : Memory m n Γ
    e : Expr m n

data InstructionStep {m} : (M : Env m) → Instruction m (proj₁ M) → Env m → Set where 
    alloca-step : ∀ {t : Type} → InstructionStep (⟨ ρ ⟩) (alloca t) (⟨ new t ρ ⟩)
    store-step : ∀ {x : Var m n} {e : Expr m n} {ρ : Memory m n Γ} → (i@(v , _) : Init ρ e) → 
        InstructionStep (⟨ ρ ⟩) (store e x) ⟨ set ρ (toAddress x) v  ⟩ 
    load-step : ∀ {x : Var m n} (i@(v , _) : IsJust (ρ (toAddress x))) →
        InstructionStep (⟨ ρ ⟩) (load x) ⟨ new-init v ρ ⟩ 
    offset-step : 
        ∀ {o : Offset} {x : Var m n} {α@(y , b₁) : Address m n Γ} {b₂ b₃ : BoundedOffset y Γ} 
        (voff : toOffset b₁ ≡ o) (vρ : just (pointer α) ≡ ρ (toAddress x)) (vadd : AddBounded b₁ b₂ b₃) →
        InstructionStep (⟨ ρ ⟩) (offset x o) ⟨ new-init (pointer (y , b₃)) ρ ⟩
    
 