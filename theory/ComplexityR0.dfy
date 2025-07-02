include "./math/ExpReal.dfy"
include "./math/Factorial.dfy"
include "./math/FloorCeil.dfy"
include "./math/LogNat.dfy"
include "./math/SqrtNat.dfy"
include "./math/TypeR0.dfy"

/**************************************************************************
  Complexity definitions lifted for non-negative real codomain
**************************************************************************/

module ComplexityR0 { 
  import opened ExpReal
  import opened Factorial  
  import opened FloorCeil   
  import opened LogNat
  import opened SqrtNat
  import opened TypeR0 

  /* Big O */

  ghost predicate bigO(f:nat->R0, g:nat->R0)
  { 
    exists c:R0, n0:nat :: bigOfrom(c, n0, f, g) 
  }

  ghost predicate bigOfrom(c:R0, n0:nat, f:nat->R0, g:nat->R0)
  {
    forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n)
  }

  ghost predicate tIsBigO(n:nat, t:R0, g:nat->R0)
  { 
    exists f:nat->R0 :: t <= f(n) && bigO(f,g)
  }

  ghost predicate isBigOPoly(f:nat->R0)
  { 
    exists k:R0 :: bigO(f, n => pow(n as R0, k))
  }

  /* Big Ω */

  ghost predicate bigOmega(f:nat->R0, g:nat->R0)
  { 
    exists c:R0, n0:nat :: bigOmegaFrom(c, n0, f, g) 
  }

  ghost predicate bigOmegaFrom(c:R0, n0:nat, f:nat->R0, g:nat->R0)
  {
    forall n:nat :: 0 <= n0 <= n ==> c*g(n) <= f(n)
  }

  ghost predicate tIsBigOmega(n:nat, t:R0, g:nat->R0)
  { 
    exists f:nat->R0 :: f(n) <= t && bigOmega(f, g)
  }

  /* Big Θ */

  ghost predicate bigTheta1(f:nat->R0, g:nat->R0)
  { 
    bigOmega(f, g) && bigO(f, g) 
  }

  ghost predicate bigTheta2(f:nat->R0, g:nat->R0)
  { 
    exists c1:R0, c2:R0, n0:nat :: bigThetaFrom(c1, c2, n0, f, g) 
  }

  ghost predicate bigThetaFrom(c1:R0, c2:R0, n0:nat, f:nat->R0, g:nat->R0)
  {
    forall n:nat :: 0 <= n0 <= n ==> c1*g(n) <= f(n) <= c2*g(n)  
  }

  /* Common growth rates */

  ghost function constGrowth() : nat->R0
  {   
    n => 1.0
  }

  ghost function logGrowth() : nat->R0
  {   
    n => if n>0 then log2(n) as R0 else 0.0
  }

  ghost function logGrowth2() : nat->R0
  {   
    n => log2(n+1) as R0
  }

  ghost function sqrtGrowth() : nat->R0
  {   
    n => sqrt(n) as R0
  }

  ghost function linGrowth() : nat->R0
  {   
    n => pow(n as R0, 1.0)
  }

  ghost function quadGrowth() : nat->R0
  {   
    n => pow(n as R0, 2.0)
  }

  ghost function cubicGrowth() : nat->R0
  {   
    n => pow(n as R0, 3.0)
  }

  ghost function polyGrowth(k:R0) : nat->R0
  {   
    n => pow(n as R0, k)
  }

  ghost function expGrowth() : nat->R0
  {   
    n => pow(2.0, n as R0)
  }

  ghost function facGrowth() : nat->R0
  {   
    n => fac(n) as R0
  }

  ghost function dexpGrowth() : nat->R0
  {   
    n => pow(2.0, pow(2.0, n as R0))
  }

}