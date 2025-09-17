include "./Order.dfy"
include "./Order2.dfy"
include "./TypeR0.dfy"

/******************************************************************************
  Utils for functions
******************************************************************************/

module Function {

  import opened TypeR0

  /******************************************************************************
    Liftings
  ******************************************************************************/

  ghost function liftD<T>(f:nat->T, default:T) : int->T
  {
    k => if k < 0 then default else f(k as nat)
  }

  ghost function liftCi2r(f:int->int) : int->real
  {
    n => f(n) as real
  }

  // Lift f:nat->nat to f':nat->R0
  ghost function liftToR0(f:nat->nat) : nat->R0
  {
    n => f(n) as R0
  }

  /******************************************************************************
    Function predicates
  ******************************************************************************/

  ghost predicate EventuallyConst(f:nat->R0, a:R0, n0:nat)
  {
    forall n:nat :: n >= n0 ==> f(n) == a
  }   

  ghost predicate EventuallyZero(f:nat->R0, n0:nat)
  {
    EventuallyConst(f, 0.0, n0)
  }   

  ghost predicate AlwaysConst(f:nat->R0, a:R0)
  {
    EventuallyConst(f, a, 0)
  }   

  ghost predicate AlwaysZero(f:nat->R0)
  {
    EventuallyConst(f, 0.0, 0)
  }     

  ghost predicate EventuallyConstBoundAbove(f:nat->R0, a:R0, n0:nat)
  {
    forall n:nat :: n >= n0 ==> f(n) <= a
  }    

  ghost predicate AlwaysConstBoundAbove(f:nat->R0, a:R0)
  {
    EventuallyConstBoundAbove(f, a, 0)
  } 

  ghost predicate EventuallyConstBoundBelow(f:nat->R0, a:R0, n0:nat)
  {
    forall n:nat :: n >= n0 ==> f(n) >= a
  }    

  ghost predicate AlwaysConstBoundBelow(f:nat->R0, a:R0)
  {
    EventuallyConstBoundBelow(f, a, 0)
  }             

  /******************************************************************************
    Operators on set of functions
  ******************************************************************************/

  // a*A = {a*f ​∣ f ​∈ A}  where a > 0
  ghost function scaleSet(a:R0, A:iset<nat->R0>): iset<nat->R0>
    requires a > 0.0
  {
    iset h:nat->R0 | exists f1 :: f1 in A && h == (n => a * f1(n))
  }

  // A+B = {f1​+f2 ​∣ f1 ​∈ A, f2 ​∈ B}
  ghost function sumSet(A:iset<nat->R0>, B:iset<nat->R0>): iset<nat->R0>
  {
    iset h:nat->R0 | exists f1, f2 :: f1 in A && f2 in B && h == (n => f1(n) + f2(n))
  }

  // A*B = {f1​*f2 ​∣ f1 ​∈ A, f2 ​∈ B}
  ghost function mulSet(A:iset<nat->R0>, B:iset<nat->R0>): iset<nat->R0>
  {
    iset h:nat->R0 | exists f1, f2 :: f1 in A && f2 in B && h == (n => f1(n) * f2(n))
  }

}