include "./TypeR0.dfy"

/******************************************************************************
  Functions
******************************************************************************/

module LemFunction {
  import opened TypeR0

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

  lemma {:axiom} lem_funExt<A,B>(f1:A->B, f2:A->B)
    requires forall x:A :: f1(x) == f2(x)
    ensures f1 == f2

}