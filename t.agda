-- This is the formalization of parts of the report
-- I am still struggling to understand the context, so I postulated the permutation lemmas
open import Data.Product
open import Agda.Builtin.Equality
open import Data.String
open import Relation.Nullary
open import Data.Sum
  

module T  where



    data Typ : Set where
        ℕ : Typ
        _⇒_ : Typ -> Typ -> Typ


    data Exp : Set where
        var : (varname : String) -> Exp
        z : Exp
        s : (pred : Exp) -> Exp
        rec : (e₀ : Exp) -> (e₁ : Σ String (λ x -> Σ String (λ y -> Exp))) -> (e : Exp) -> Exp
        lam : (e : (Σ String (λ x → Exp))) -> Exp
        app : (e₁ : Exp)  -> (e₂ : Exp)  -> Exp

    Typ1 =  Σ String (λ x -> Σ String (λ y -> Exp))

    data Context : Set where
        empty : Context
        _∪_ : Context -> (String × Typ)  -> Context

    infix 9 _⊢_∷_ 
    infix 9 _↦_ 
    infix 9 _val 
    infixr 10 [_/_]_
    infix 10 _∪_


    data _⊢_∷_ : (Γ : Context) (e : Exp) (τ : Typ) -> Set  where
        var-refl : {Γ' : Context} {x : String} {τ : Typ} -> (Γ' ∪ (x , τ) ) ⊢ (var x) ∷ τ 
        nat-intro-z : {Γ : Context} -> Γ ⊢ z ∷ ℕ
        nat-intro-s : {Γ : Context} {e : Exp} -> Γ ⊢ e ∷ ℕ -> Γ ⊢ s e ∷ ℕ
        nat-elim :  {Γ : Context} {e₀ : Exp} {x y : String} {e₁ : Exp} {e : Exp}  {τ : Typ}
                    -> Γ ⊢ e ∷ ℕ -> Γ ⊢ e₀ ∷ τ -> (Γ ∪ (x , ℕ)) ∪ ( y , τ) ⊢ e₁ ∷ τ
                    -> Γ ⊢ rec e₀ (x , (y , e₁)) e ∷ τ 
        arrow-intro : {Γ : Context} {x : String} {e :  Exp} {τ₁ τ₂ : Typ}
                    -> ( Γ ∪ (x , τ₁) ) ⊢  e ∷ τ₂ 
                    -> Γ ⊢ lam ( x , e) ∷ (τ₁ ⇒ τ₂)
        arrow-elim :  {Γ : Context}  {τ₁ τ₂ : Typ} {e₁ e₂ : Exp }
                    -> Γ ⊢ e₁ ∷ τ₁ ⇒ τ₂ -> Γ ⊢ e₂ ∷ τ₁
                    -> Γ ⊢ app e₁ e₂ ∷ τ₂

    data _val : (e : Exp)  -> Set where 
        z-val : z val
        s-val : {e : Exp} -> s e val
        lam-val : { e : (Σ String (λ x → Exp)) } -> lam e val

    [_/_]_ : (e₂ : Exp) (x : String) (e₁ : Exp) -> Exp
    [ e₂ / x ] (var varname) with varname ≟ x
    ... | Relation.Nullary.Dec.yes p = e₂
    ... | Relation.Nullary.Dec.no ¬p = var varname
    [ e₂ / x ] z = z
    [ e₂ / x ] s e₁ = s ([ e₂ / x ] e₁ )
    [ e₂ / x ] rec e₁ e₃@( x' , ( y' , e3)) e with x' ≟ x | y' ≟ x
    ([ e₂ / x ] rec e₁ (x' , y' , e3) e) | no _ | no _  = rec ( [ e₂ / x ] e₁) (x' , (y' , [ e₂ / x ] e3))  ([ e₂ / x ] e)
    ([ e₂ / x ] rec e₁ (x' , y' , e3) e) | _ | _ =  rec ( [ e₂ / x ] e₁) (x' , (y' , e3))  ([ e₂ / x ] e)
    [ e₂ / x ] lam (x' , e) with x' ≟ x
    ([ e₂ / x ] lam (x' , e)) | no ¬p = lam ( (x' , [ e₂ / x ] e))
    ([ e₂ / x ] lam (x' , e)) | yes p = lam (x' , e)
    [ e₂ / x ] app e₁ e₃ = app ( [ e₂ / x ] e₁) ( [ e₂ / x ] e₃)



    data _↦_ :  (e e' : Exp) -> Set where
        app-func : { e₂ e₁ e₁' : Exp } -> e₁ ↦ e₁' -> app e₁ e₂ ↦ app e₁' e₂
        app-beta : {x : String} {e e₂ : Exp} -> app (lam (x , e)) e₂ ↦ [ e₂ / x ] e
        rec-arg : { e e' e₀ : Exp} { e₁ : Typ1 }  -> e ↦ e' -> rec e₀ e₁ e ↦ rec e₀ e₁ e'
        rec-z : { e₀ : Exp} { e₁ : Typ1 }  -> rec e₀ e₁ z ↦ e₀ 
        rec-s : { e e₀ : Exp} {x y : String} { e₁ : Exp }   -> rec e₀ (x , y , e₁) (s e) ↦ [ e / x ] [ rec e₀ ( x , y , e₁) e / y ] e₁

    postulate
        permutation :  {Γ : Context} {e : Exp} {τ τ' τ'' : Typ} {x y : String} -> (Γ ∪ (x , τ')) ∪ (y ,  τ'') ⊢ e ∷ τ -> (Γ ∪ (y , τ'' )) ∪ (x , τ') ⊢ e ∷ τ
        permutation3 :  {Γ : Context} {e : Exp} {τ τ' τ'' τ''' : Typ} {x y z : String} -> ((Γ ∪ (x , τ')) ∪ (y , τ'')) ∪ (z ,  τ''') ⊢ e ∷ τ -> ((Γ ∪ (z , τ''')) ∪ (x , τ' )) ∪ (y , τ'') ⊢ e ∷ τ
        permutation3' :  {Γ : Context} {e : Exp} {τ τ' τ'' τ''' : Typ} {x y z : String} -> ((Γ ∪ (x , τ')) ∪ (y , τ'')) ∪ (z ,  τ''') ⊢ e ∷ τ -> ((Γ ∪ (y , τ'')) ∪ (z , τ''' )) ∪ (x , τ') ⊢ e ∷ τ
        permutation3'' :  {Γ : Context} {e : Exp} {τ τ' τ'' τ''' : Typ} {x y z : String} -> ((Γ ∪ (x , τ')) ∪ (y , τ'')) ∪ (z ,  τ''') ⊢ e ∷ τ -> ((Γ ∪ (y , τ'')) ∪ (x , τ' )) ∪ (z , τ''') ⊢ e ∷ τ

        replacement : {Γ : Context} {e : Exp} {τ τ' τ''  : Typ} {x y : String} ->  y ≡ x -> ( Γ ∪ ( x , τ' ))  ∪ (y , τ'') ⊢ e ∷ τ -> Γ ∪ ( y , τ'') ⊢ e ∷ τ 

    weakening :  {Γ : Context} {e : Exp} {τ τ' : Typ} {x : String} -> Γ ⊢ e ∷ τ -> Γ ∪ (x , τ') ⊢ e ∷ τ
    weakening var-refl = permutation var-refl
    weakening nat-intro-z = nat-intro-z
    weakening (nat-intro-s p) = nat-intro-s (weakening p)
    weakening (nat-elim p p₁ p₂) = nat-elim (weakening p) (weakening p₁ ) (permutation3 (weakening  p₂ ))
    weakening (arrow-intro p) = arrow-intro (permutation (weakening p))
    weakening (arrow-elim p p₁) = arrow-elim (weakening p) (weakening p₁)



    substitution :   {Γ : Context} {e e' : Exp} {τ τ' : Typ} {x : String}
                    -> Γ ⊢ e' ∷ τ' -> Γ ∪ (x , τ') ⊢ e ∷ τ -> Γ ⊢ [ e' / x ] e ∷ τ
    substitution {x = x} p var-refl with x ≟ x
    substitution {x = x} p var-refl | yes p₁ = p
    substitution {x = x} p var-refl | no ¬p with ¬p refl
    substitution {x = x} p var-refl | no ¬p | ()
    substitution p nat-intro-z = nat-intro-z
    substitution p (nat-intro-s p') = nat-intro-s (substitution p p')
    substitution {x = x} p (nat-elim {x = x'}{y = y'} p' p'' p''') with  x' ≟ x | y' ≟ x
    substitution {x = x} p (nat-elim {x = x'} {y'} p' p'' p''') | no ¬q | no ¬q' = nat-elim (substitution p p') (substitution p p'') (substitution (weakening (weakening p)) (permutation3' p'''))
    substitution {x = x} p (nat-elim {x = x'} {y'} p' p'' p''') | no ¬q | yes q' = nat-elim (substitution p p') (substitution p p'') (replacement q' (permutation3'' p'''))
    substitution {x = x} p (nat-elim {x = x'} {y'} p' p'' p''') | yes q | _ = nat-elim (substitution p p') (substitution p p'') (permutation (replacement q (permutation3 p''')))
    substitution {e = lam (x' , e'') } {x = x}  p (arrow-intro p') with x' ≟ x
    substitution {_} {lam (x' , e'')} {x = x} p (arrow-intro p') | yes q = arrow-intro (replacement q p')
    substitution {_} {lam (x' , e'')} {x = x} p (arrow-intro p') | no ¬q = arrow-intro (substitution (weakening p) (permutation p'))
    substitution p (arrow-elim p' p'') = arrow-elim (substitution p p') (substitution p p'')


    preservation : { e e' : Exp } { τ : Typ}
                   -> empty ⊢ e ∷ τ -> e ↦ e' -> empty ⊢ e' ∷ τ
    preservation (arrow-elim p p') (app-func q) = arrow-elim (preservation p q) p'
    preservation (arrow-elim (arrow-intro p) p') app-beta = substitution p' p
    preservation (nat-elim p p' p'') (rec-arg q) = nat-elim (preservation p q) p' p''
    preservation (nat-elim p p' p'') rec-z = p'
    preservation (nat-elim (nat-intro-s p) p' p'') rec-s = substitution p (substitution (nat-elim (weakening p) (weakening p') (permutation3 (weakening p''))) p'')

    progress :  { e : Exp } { τ : Typ}
                -> empty ⊢ e ∷ τ -> e val ⊎ Σ Exp (λ e' -> e ↦ e')
    progress nat-intro-z = inj₁ z-val
    progress (nat-intro-s p) = inj₁ s-val
    progress (nat-elim p p' p'') with progress p
    progress (nat-elim p p' p'') | inj₁ z-val = inj₂ (_ , rec-z)
    progress (nat-elim p p' p'') | inj₁ s-val = inj₂ (_ , rec-s)
    progress (nat-elim p p' p'') | inj₂ (e' , q) = inj₂ (_ , (rec-arg q))
    progress (arrow-intro p) = inj₁ lam-val
    progress (arrow-elim p p') with progress p
    progress (arrow-elim p p') | inj₁ lam-val = inj₂ (_ , app-beta)
    progress (arrow-elim p p') | inj₂ (e' , q) = inj₂ (_ , (app-func q))


