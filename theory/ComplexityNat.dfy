include "./math/ExpNat.dfy"
include "./math/Factorial.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemFunction.dfy"
include "./math/LogNat.dfy"
include "./math/SqrtNat.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityR0.dfy"

/**************************************************************************
  Complexity definitions for non-negative integer functions
**************************************************************************/

module ComplexityNat { 
  import opened ExpNat
  import opened Factorial  
  import opened FloorCeil   
  import opened LemFunction
  import opened LogNat
  import opened SqrtNat
  import opened TypeR0 
  import CR0 = ComplexityR0

  /* Big O */

  ghost predicate bigO(f:nat->nat, g:nat->nat)
  { 
    exists c:nat, n0:nat :: bigOfrom(c, n0, f, g) 
  }

  ghost predicate bigOfrom(c:nat, n0:nat, f:nat->nat, g:nat->nat)
  {
    forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n)  
  }

  ghost predicate tIsBigO(n:nat, t:nat, g:nat->nat)
  { 
    exists f:nat->nat :: t <= f(n) && bigO(f,g)
  }

  ghost predicate isBigOPoly(f:nat->nat)
  { 
    exists k:nat :: bigO(f, n => pow(n,k))
  }

  /* Big Ω */

  ghost predicate bigOmega(f:nat->nat, g:nat->nat)
  { 
    exists c:nat, n0:nat :: bigOmegaFrom(c, n0, f, g) 
  }

  ghost predicate bigOmegaFrom(c:nat, n0:nat, f:nat->nat, g:nat->nat)
  {
    forall n:nat :: 0 <= n0 <= n ==> c*g(n) <= f(n)
  }

  ghost predicate tIsBigOmega(n:nat, t:nat, g:nat->nat)
  { 
    exists f:nat->nat :: f(n) <= t && bigOmega(f, g)
  }

  /* Big Θ */

  ghost predicate bigTheta1(f:nat->nat, g:nat->nat)
  { 
    bigOmega(f, g) && bigO(f, g) 
  }

  ghost predicate bigTheta2(f:nat->nat, g:nat->nat)
  { 
    exists c1:nat, c2:nat, n0:nat :: bigThetaFrom(c1, c2, n0, f, g) 
  }

  ghost predicate bigThetaFrom(c1:nat, c2:nat, n0:nat, f:nat->nat, g:nat->nat)
  {
    forall n:nat :: 0 <= n0 <= n ==> c1*g(n) <= f(n) <= c2*g(n)  
  }
  
  /* Common growth rates */

  ghost function constGrowth() : nat->nat
  {   
    n => 1
  }

  ghost function logGrowth() : nat->nat
  {   
    n => if n>0 then log2(n) else 0
  }

  ghost function logGrowth2() : nat->nat
  {   
    n => log2(n+1)
  }

  ghost function sqrtGrowth() : nat->nat
  {   
    n => sqrt(n)
  }

  ghost function linGrowth() : nat->nat
  {   
    n => pow(n,1)
  }

  ghost function quadGrowth() : nat->nat
  {   
    n => pow(n,2)
  }

  ghost function cubicGrowth() : nat->nat
  {   
    n => pow(n,3)
  }

  ghost function polyGrowth(k:nat) : nat->nat
  {   
    n => pow(n,k)
  }

  ghost function expGrowth() : nat->nat
  {   
    n => pow(2,n)
  }

  ghost function facGrowth() : nat->nat
  {   
    n => fac(n)
  }

  ghost function dexpGrowth() : nat->nat
  {   
    n => pow(2,pow(2,n))
  }

}