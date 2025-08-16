include "./math/ExpNat.dfy"
include "./math/Factorial.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemFunction.dfy"
include "./math/Log2Nat.dfy"
include "./math/SqrtNat.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityR0.dfy"

/******************************************************************************
  Complexity definitions for non-negative integer functions
******************************************************************************/

module ComplexityNat { 
  import opened ExpNat
  import opened Factorial  
  import opened FloorCeil   
  import opened LemFunction
  import opened Log2Nat
  import opened SqrtNat
  import opened TypeR0 
  import CR0 = ComplexityR0

  /******************************************************************************
    Big O
  ******************************************************************************/

  ghost predicate bigO(f:nat->nat, g:nat->nat)
  { 
    exists c:nat, n0:nat :: bigOfrom(c, n0, f, g) 
  }

  ghost predicate bigOfrom(c:nat, n0:nat, f:nat->nat, g:nat->nat)
  {
    forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n)  
  }

  // bigO(f,g) <=> f ∈ O(g) 
  ghost function O(g:nat->nat): iset<nat->nat>
  {
    iset f:nat->nat | bigO(f, g)
  }    

  ghost predicate tIsBigO(n:nat, t:nat, g:nat->nat)
  { 
    exists f:nat->nat :: t <= f(n) && f in O(g)
  }

  ghost predicate isBigOPoly(f:nat->nat)
  { 
    exists k:nat :: bigO(f, n => exp(n,k))
  }

  /******************************************************************************
    Big Ω
  ******************************************************************************/

  ghost predicate bigOm(f:nat->nat, g:nat->nat)
  { 
    exists c:nat, n0:nat :: bigOmFrom(c, n0, f, g) 
  }

  ghost predicate bigOmFrom(c:nat, n0:nat, f:nat->nat, g:nat->nat)
  {
    forall n:nat :: 0 <= n0 <= n ==> c*g(n) <= f(n)
  }

  // bigOm(f,g) <=> f ∈ Ω(g)
  ghost function Om(g:nat->nat): iset<nat->nat>
  {
    iset f:nat->nat | bigOm(f, g)
  }   

  ghost predicate tIsBigOm(n:nat, t:nat, g:nat->nat)
  { 
    exists f:nat->nat :: f(n) <= t && f in Om(g)
  } 

  /******************************************************************************
    Big Θ
  ******************************************************************************/

  // 1st def. of Big Θ as the intersection of Big O and Big Ω
  ghost predicate bigTh(f:nat->nat, g:nat->nat)
  { 
    f in Om(g) && f in O(g) 
  }

  // bigTh(f,g) <=> f ∈ Θ(g)
  ghost function Th(g:nat->nat): iset<nat->nat>
  {
    iset f:nat->nat | bigTh(f, g)
  }

  // 2nd def. of Big Θ
  ghost predicate bigTh2(f:nat->nat, g:nat->nat)
  { 
    exists c1:nat, c2:nat, n0:nat :: bigThFrom(c1, c2, n0, f, g) 
  }

  ghost predicate bigThFrom(c1:nat, c2:nat, n0:nat, f:nat->nat, g:nat->nat)
  {
    forall n:nat :: 0 <= n0 <= n ==> c1*g(n) <= f(n) <= c2*g(n)  
  }     

  ghost predicate tIsBigTh(n:nat, t:nat, g:nat->nat)
  { 
    tIsBigOm(n, t, g) && tIsBigO(n, t, g)
  }   
  
  /******************************************************************************
    Common growth rates
  ******************************************************************************/

  ghost function constGrowth() : nat->nat
  {   
    n => 1
  }

  ghost function log2Growth() : nat->nat
  {   
    n => if n>0 then log2(n) else 0
  }

  ghost function log2Plus1Growth() : nat->nat
  {   
    n => log2(n+1)
  }

  ghost function sqrtGrowth() : nat->nat
  {   
    n => sqrt(n)
  }

  ghost function linGrowth() : nat->nat
  {   
    n => exp(n,1)
  }

  ghost function quadGrowth() : nat->nat
  {   
    n => exp(n,2)
  }

  ghost function cubicGrowth() : nat->nat
  {   
    n => exp(n,3)
  }

  ghost function polyGrowth(k:nat) : nat->nat
  {   
    n => exp(n,k)
  }

  ghost function expGrowth(b:nat) : nat->nat
  {   
    n => exp(b, n)
  }

  ghost function exp2Growth() : nat->nat
  {   
    n => exp2(n)
  }

  ghost function facGrowth() : nat->nat
  {   
    n => fac(n)
  }

  ghost function dexp2Growth() : nat->nat
  {   
    n => exp2(exp2(n))
  }

}