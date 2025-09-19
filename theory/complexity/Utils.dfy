include "../math/LemFunction.dfy"
include "../math/intervalOp/SumReal.dfy"
include "../math/TypeR0.dfy"

/******************************************************************************
  Utils for complexity
******************************************************************************/

module Utils { 

  import opened LemFunction
  import opened SumReal
  import opened TypeR0

  /******************************************************************************
    A special case of sum
  ******************************************************************************/

  // λn.Σ_{k=1}^{m}f(n)
  opaque ghost function replSum(m:nat, f:nat->R0): nat->R0 {
    (n:nat) => lem_NonNegative(1, m, k => f(n)); sum(1, m, k => f(n)) as R0
  } 

  // λn.Σ_{k=1}^{m}f(n) = λn.m*f(n)
  lemma lem_ReplSumSimpl(m:nat, f:nat->R0)
    ensures replSum(m, f) == (n => m as R0 * f(n))
  {
    reveal replSum();
    forall n:nat ensures replSum(m, f)(n) == (n => m as R0 * f(n))(n)
    {
      
    }
    lem_Exten(replSum(m, f), n => m as R0 * f(n));
  }

}