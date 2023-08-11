# github.io


Constructing ZF Set Theory in Agda 
============

Shinji KONO (kono@ie.u-ryukyu.ac.jp), University of the Ryukyus
## ZF in Agda

[code ](https://github.com/shinji-kono/) github 

[zf](html/zf.html)  axiom of ZF

[zfc](html/zfc.html) axiom of choice

[NSet](html/NSet.html)  Naive Set Theory

[Ordinals](html/Ordinals.html)  axiom of Ordinals

[OD](html/OD.html)   a model of ZF based on Ordinal Definable Set with assumptions

[ODC](html/ODC.html)   Law of exclude middle from axiom of choice assumptions

[LEMC](html/LEMC.html) choice with assumption of the Law of exclude middle 

[BAlgebra](html/BAlgebra.html) Boolean algebra on OD (not yet done)

[zorn](html/zorn.html)  Zorn lemma

[Topology](html/Topology.html)  Topology

[Tychonoff](html/Tychonoff.html)

[VL](html/VL.html)  V and L

[cardinal](html/cardinal.html) Cardinals

[filter](html/filter.html) Filter

[filter-util](html/filter-util.html) Projection of Filter

[generic-filter](html/generic-filter.html) Generic Filter

[maximum-filter](html/maximum-filter.html) Maximum filter by Zorn lemma

[ordinal](html/ordinal.html)   countable model of Ordinals

[ZProduct](html/ZProduct.html)

[OrdUtil](html/OrdUtil.html)

[PFOD](html/PFOD.html)


## Ordinal Definable Set

It is a predicate has an Ordinal argument.

In Agda, OD is defined as follows.

```
    record OD : Set (suc n ) where
      field
        def : (x : Ordinal  ) → Set n
```

This is not a ZF Set, because it can contain entire Ordinals.

## HOD : Hereditarily Ordinal Definable

What we need is a bounded OD, the containment is limited by an ordinal.

```
    record HOD : Set (suc n) where
      field
        od : OD
        odmax : Ordinal
        <odmax : {y : Ordinal} → def od y → y o< odmax
```

In classical Set Theory, HOD stands for Hereditarily Ordinal Definable, which means

```
     HOD = { x | TC x ⊆ OD }
```

TC x is all transitive closure of x, that is elements of x and following all elements of them are all OD. But 
what is x? In this case, x is an Set which we don't have yet. In our case, HOD is a bounded OD. 

## 1 to 1 mapping between an HOD and an Ordinal

HOD is a predicate on Ordinals and the solution is bounded by some ordinal. If we have a mapping

```
  od→ord : HOD  → Ordinal 
  ord→od : Ordinal  → HOD  
  oiso   :  {x : HOD }      → ord→od ( od→ord x ) ≡ x
  diso   :  {x : Ordinal } → od→ord ( ord→od x ) ≡ x
```

we can check an HOD is an element of the OD using def.

A ∋ x can be define as follows.

```
    _∋_ : ( A x : HOD  ) → Set n
    _∋_  A x  = def (od A) ( od→ord x )

```
In ψ : Ordinal → Set,  if A is a  record { od = { def = λ x → ψ x } ...}  , then

    A ∋ x = def (od A) ( od→ord x ) = ψ (od→ord x)

They say the existing of the mappings can be proved in Classical Set Theory, but we
simply assumes these non constructively.

