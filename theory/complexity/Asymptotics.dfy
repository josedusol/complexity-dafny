include "../math/ExpReal.dfy"
include "../math/Factorial.dfy"
include "../math/FloorCeil.dfy"
include "../math/Log2Real.dfy"
include "../math/LogReal.dfy"
include "../math/Root2Real.dfy"
include "../math/RootReal.dfy"
include "../math/TypeR0.dfy"

/******************************************************************************
  Asymptotics definitions
******************************************************************************/

module Asymptotics { 

  import Exp = ExpReal
  import opened Factorial  
  import opened FloorCeil   
  import Log2  = Log2Real
  import Log   = LogReal
  import Root2 = Root2Real
  import Root  = RootReal
  import opened TypeR0

  /******************************************************************************
    Big Oh Notation - O
  ******************************************************************************/

  // Def. of O as a relation 
  ghost predicate bigOh(f:nat->R0, g:nat->R0)
  { 
    exists c:R0, n0:nat :: c > 0.0 && bigOhFrom(c, n0, f, g) 
  }

  ghost predicate bigOhFrom(c:R0, n0:nat, f:nat->R0, g:nat->R0)
  {
    forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n)
  }

  // Def. of O as a class
  // f ∈ O(g) ⟺ bigOh(f,g)
  ghost function O(g:nat->R0): iset<nat->R0>
  {
    iset f:nat->R0 | bigOh(f, g)
  }

  // A program counter t is O(g) for input size n
  ghost predicate tIsBigOh(n:nat, t:R0, g:nat->R0)
  { 
    exists f:nat->R0 :: t <= f(n) && f in O(g)
  }

  ghost predicate isBigOhPoly(f:nat->R0)
  { 
    exists k:R0 :: f in O(n => Exp.exp(n as R0, k))
  }

  /******************************************************************************
    Big Omega Notation - Ω
  ******************************************************************************/

  // Def. of Ω as a relation 
  ghost predicate bigOm(f:nat->R0, g:nat->R0)
  { 
    exists c:R0, n0:nat :: c > 0.0 && bigOmFrom(c, n0, f, g)
  }

  ghost predicate bigOmFrom(c:R0, n0:nat, f:nat->R0, g:nat->R0)
  {
    forall n:nat :: 0 <= n0 <= n ==> c*g(n) <= f(n)
  }

  // Def. of Ω as a class
  // f ∈ Ω(g) ⟺ bigOm(f,g)
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

  // 1st def. of Θ as relation
  ghost predicate bigTh(f:nat->R0, g:nat->R0)
  { 
    exists c1:R0, c2:R0, n0:nat :: c1 > 0.0 && c2 > 0.0 && bigThFrom(c1, c2, n0, f, g) 
  }

  ghost predicate bigThFrom(c1:R0, c2:R0, n0:nat, f:nat->R0, g:nat->R0)
  {
    forall n:nat :: 0 <= n0 <= n ==> c1*g(n) <= f(n) <= c2*g(n)  
  }

  // Def. of Θ as a class
  // f ∈ Θ(g) ⟺ bigTh(f,g) 
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
    tIsBigOm(n, t, g) && tIsBigOh(n, t, g)
  }    

  /******************************************************************************
    Common growth rates
  ******************************************************************************/

  // 0
  ghost function zeroGrowth() : nat->R0
  {   
    n => 0.0
  }

  // 1
  ghost function constGrowth() : nat->R0
  {   
    n => 1.0
  }

  // lob_b(n)
  ghost function logGrowth(b:R0) : nat->R0
    requires b > 1.0
  {   
    Log.lem_NonNegativeAuto();
    n => if n > 0 then Log.log(b, n as R0) else 0.0
  }

  // log_b(n+1)
  ghost function logPlus1Growth(b:R0) : nat->R0
    requires b > 1.0
  {   
    Log.lem_NonNegativeAuto();
    n => Log.log(b, (n+1) as R0)
  }

  // log_2(n)
  ghost function log2Growth() : nat->R0
  {   
    n => if n > 0 then Log2.log2(n as R0) else 0.0
  }

  // log_2(n+1)
  ghost function log2Plus1Growth() : nat->R0 
  {   
    n => Log2.log2((n+1) as R0) 
  }
 
  // ᵏ√n
  ghost function rootGrowth(k:R0) : nat->R0
    requires k > 0.0
  {   
    Root.lem_NonNegativeAuto();
    n => Root.root(n as R0, k)
  }

  // √n
  ghost function sqrtGrowth() : nat->R0
  {   
    n => Root2.sqrt(n as R0)
  }

  // n
  ghost function linGrowth() : nat->R0
  {   
    n => n as R0
  }

  // n^2
  ghost function quadGrowth() : nat->R0
  {   
    n => (n*n) as R0
  }

  // n^3
  ghost function cubicGrowth() : nat->R0
  {   
    n => (n*n*n) as R0
  }

  // n^k
  ghost function polyGrowth(k:R0) : nat->R0
  {   
    n => Exp.exp(n as R0, k)
  }

  // b^n
  ghost function expGrowth(b:R0) : nat->R0
  {   
    n => Exp.exp(b, n as R0)
  }

  // 2^n
  ghost function exp2Growth() : nat->R0
  {   
    n => Exp.exp2(n as R0) 
  }

  // n!
  ghost function facGrowth() : nat->R0
  {   
    n => fac(n) as R0
  }

  // 2^(2^n)
  ghost function dexp2Growth() : nat->R0
  {   
    n => Exp.exp2(Exp.exp2(n as R0))
  }

}