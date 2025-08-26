include "./math/ExpReal.dfy"
include "./math/Factorial.dfy"
include "./math/FloorCeil.dfy"
include "./math/LogReal.dfy"
include "./math/SqrtNat.dfy"
include "./math/TypeR0.dfy"

/******************************************************************************
  Complexity definitions lifted for non-negative real codomain
******************************************************************************/

module ComplexityR0 { 
  import opened ExpReal
  import opened Factorial  
  import opened FloorCeil   
  import opened LogReal
  import opened SqrtNat
  import opened TypeR0 

  /******************************************************************************
    Big Oh Notation - O
  ******************************************************************************/

  // Def. of O relation 
  ghost predicate bigO(f:nat->R0, g:nat->R0)
  { 
    exists c:R0, n0:nat :: bigOfrom(c, n0, f, g) 
  }

  ghost predicate bigOfrom(c:R0, n0:nat, f:nat->R0, g:nat->R0)
  {
    forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n)
  }

  // Def. of O class
  // bigO(f,g) <=> f ∈ O(g) 
  ghost function O(g:nat->R0): iset<nat->R0>
  {
    iset f:nat->R0 | bigO(f, g)
  }

  // A program counter t is O(g) for input size n
  ghost predicate tIsBigO(n:nat, t:R0, g:nat->R0)
  { 
    exists f:nat->R0 :: t <= f(n) && f in O(g)
  }

  ghost predicate isBigOPoly(f:nat->R0)
  { 
    exists k:R0 :: bigO(f, n => exp(n as R0, k))
  }

  /******************************************************************************
    Big Omega Notation - Ω
  ******************************************************************************/

  // Def. of Ω relation 
  ghost predicate bigOm(f:nat->R0, g:nat->R0)
  { 
    exists c:R0, n0:nat :: bigOmFrom(c, n0, f, g) 
  }

  ghost predicate bigOmFrom(c:R0, n0:nat, f:nat->R0, g:nat->R0)
  {
    forall n:nat :: 0 <= n0 <= n ==> c*g(n) <= f(n)
  }

  // Def. of Ω class
  // bigOm(f,g) <=> f ∈ Ω(g) 
  ghost function Om(g:nat->R0): iset<nat->R0>
  {
    iset f:nat->R0 | bigOm(f, g)
  }

  // A program counter t is Ω(g) for input size n
  ghost predicate tIsBigOm(n:nat, t:R0, g:nat->R0)
  { 
    exists f:nat->R0 :: f(n) <= t && f in Om(g)
  }

  /******************************************************************************
    Big Theta notation - Θ
  ******************************************************************************/

  // 1st def. of Θ relation
  ghost predicate bigTh(f:nat->R0, g:nat->R0)
  { 
    exists c1:R0, c2:R0, n0:nat :: bigThFrom(c1, c2, n0, f, g) 
  }

  ghost predicate bigThFrom(c1:R0, c2:R0, n0:nat, f:nat->R0, g:nat->R0)
  {
    forall n:nat :: 0 <= n0 <= n ==> c1*g(n) <= f(n) <= c2*g(n)  
  }

  // Def. of Θ class
  // bigTh(f,g) <=> f ∈ Θ(g) 
  ghost function Th(g:nat->R0): iset<nat->R0>
  {
    iset f:nat->R0 | bigTh(f, g)
  }  

  // 2nd def. of Θ relation as the intersection of O and Ω
  ghost predicate bigTh2(f:nat->R0, g:nat->R0)
  { 
    f in Om(g) && f in O(g) 
  }

  // A program counter t is Θ(g) for input size n
  ghost predicate tIsBigTh(n:nat, t:R0, g:nat->R0)
  { 
    tIsBigOm(n, t, g) && tIsBigO(n, t, g)
  }    

  /******************************************************************************
    Common growth rates
  ******************************************************************************/
  
  ghost function constGrowth() : nat->R0
  {   
    n => 1.0
  }

  ghost function logGrowth(b:R0) : nat->R0
    requires b > 1.0
  {   
    n => if n>0 then log(b, n as R0) else 0.0
  }

  ghost function logGrowth2(b:R0) : nat->R0
    requires b > 1.0
  {   
    n => log(b, (n+1) as R0) 
  }

  ghost function log2Growth() : nat->R0
  {   
    n => if n>0 then log2(n as R0) else 0.0
  }

  ghost function log2Plus1Growth() : nat->R0
  {   
    n => log2((n+1) as R0) 
  }

  ghost function sqrtGrowth() : nat->R0
  {   
    n => sqrt(n) as R0
  }

  ghost function linGrowth() : nat->R0
  {   
    n => exp(n as R0, 1.0)
  }

  ghost function quadGrowth() : nat->R0
  {   
    n => exp(n as R0, 2.0)
  }

  ghost function cubicGrowth() : nat->R0
  {   
    n => exp(n as R0, 3.0)
  }

  ghost function polyGrowth(k:R0) : nat->R0
  {   
    n => exp(n as R0, k)
  }

  ghost function expGrowth(b:R0) : nat->R0
  {   
    n => exp(b, n as R0)
  }

  ghost function exp2Growth() : nat->R0
  {   
    n => exp2(n as R0)
  }

  ghost function facGrowth() : nat->R0
  {   
    n => fac(n) as R0
  }

  ghost function dexp2Growth() : nat->R0
  {   
    n => exp2(exp2(n as R0))
  }

}