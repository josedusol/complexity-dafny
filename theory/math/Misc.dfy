include "./TypeR0.dfy"

/**************************************************************************
  Miscelanious stuff
**************************************************************************/

module Misc {
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

  // apparently useless
  ghost function ite<T>(cond: bool, thenBranch: T, elseBranch: T) : T
  {
    if cond then thenBranch else elseBranch
  }

}