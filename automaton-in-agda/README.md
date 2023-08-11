# github.io

Automaton in Agda 
============

Shinji KONO (kono@ie.u-ryukyu.ac.jp), University of the Ryukyus

## Automaton and NFA


```
record Automaton ( Q : Set ) ( Σ : Set  )
       : Set  where
    field
        δ : Q → Σ → Q
        aend : Q → Bool

record NAutomaton ( Q : Set ) ( Σ : Set  )
       : Set  where
    field
          Nδ : Q → Σ → Q → Bool
          Nend  :  Q → Bool

```

## Automaton in Agda

[automaton](html/automaton.html)   automaton definition

[nfa](html/nfa.html)               non deterministic

[sbconst2](html/sbconst2.html)     subset construction

[regular-language](html/regular-language.html) Regular Language

[regex](html/regex.html)           Regular Expression

[finiteSet](html/finiteSet.html)   Finite Set

[derive](html/derive.html)  generating FA from Regex

[pumping](html/pumping.html)  Pumping Lemma

[pumping](html/non-regular.html)  Application of Pumping Lemma

[turing](html/turing.html) Turing Machine

[halt](html/halt.html) Halting Problem

[automaton-ex](html/automaton-ex.html) 

[bijection](html/bijection.html) 

[cfg](html/cfg.html) 

[deriveUtil](html/deriveUtil.html) 

[even](html/even.html) 

[fin](html/fin.html) 

[finiteSetUtil](html/finiteSetUtil.html) 

[induction-ex](html/induction-ex.html) 

[libbijection](html/libbijection.html) 

[pushdown](html/pushdown.html) /

[puzzle](html/puzzle.html) /

[regex1-ex](html/regex1-ex.html) /

[regex2](html/regex2.html) /

[regular-concat](html/regular-concat.html) /

[regular-star](html/regular-star.html) /

[utm](html/utm.html) /


## FiniteSet

```
record FiniteSet ( Q : Set ) : Set  where
     field
        finite : ℕ
        Q←F : Fin finite → Q
        F←Q : Q → Fin finite
        finiso→ : (q : Q) → Q←F ( F←Q q ) ≡ q
        finiso← : (f : Fin finite ) → F←Q ( Q←F f ) ≡ f

fin→ : {A : Set} → FiniteSet A → FiniteSet (A → Bool ) 

```


## Regular Language

What we need is a bounded OD, the containment is limited by an ordinal.

```
record RegularLanguage ( Σ : Set ) : Set (Suc Zero) where
   field
      states : Set
      astart : states
      afin : FiniteSet states
      automaton : Automaton states Σ
   contain : List Σ → Bool
   contain x = accept automaton astart x

```

## Semantics of Regular Language

``  
    Union : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
    Union {Σ} A B x = A x  \/ B x

    split : {Σ : Set} → (x y : language {Σ} ) → language {Σ}
    split x y  [] = x [] /\ y []
    split x y (h  ∷ t) = (x [] /\ y (h  ∷ t)) \/
      split (λ t1 → x (  h ∷ t1 ))  (λ t2 → y t2 ) t

    Concat : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
    Concat {Σ} A B = split A B

    -- Terminating version of Star1
    --
    repeat : {Σ : Set} → (x : List Σ → Bool) → (y : List Σ ) → Bool 
    repeat2 : {Σ : Set} → (x : List Σ → Bool) → (pre y : List Σ ) → Bool
    repeat2 x pre [] = false
    repeat2 x pre (h ∷ y) = 
       (x (pre ++ (h ∷ [])) /\ repeat x y )
       \/ repeat2 x (pre ++ (h ∷ [])) y 

    repeat {Σ} x [] = true
    repeat {Σ} x (h ∷ y) = repeat2 x [] (h ∷ y) 

    Star : {Σ : Set} → (x : List Σ → Bool) → (y : List Σ ) → Bool 
    Star {Σ} x y = repeat x y
```

## Turing Machine

```
    record TM ( Q : Set ) ( Σ : Set  ) 
           : Set  where
        field
            automaton : Automaton  Q Σ
            tδ : Q → Σ → Write  Σ  ×  Move 
            tnone :  Σ
```

## Halting Problem

```

    record UTM : Set where
       field
          utm : TM
          encode : TM → List Bool
          is-tm : (t : TM) → (x : List Bool) → tm utm (encode t ++ x ) ≡ tm t x

    record Halt : Set where
       field
          halt :  (t : TM ) → (x : List Bool ) → Bool
          is-halt :     (t : TM ) → (x : List Bool ) → (halt t x ≡ true )  ⇔ ( (just true ≡ tm t x ) ∨ (just false ≡ tm t x ) )
          is-not-halt : (t : TM ) → (x : List Bool ) → (halt t x ≡ false ) ⇔ ( nothing ≡ tm t x )

    TNL1 : UTM → ¬ Halt 

```



