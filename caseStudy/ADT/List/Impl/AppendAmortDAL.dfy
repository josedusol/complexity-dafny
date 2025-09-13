include "../../../../theory/math/TypeR0.dfy"
include "./DynaArrayList.dfy"
include "./LemDynaArrayList.dfy"

/******************************************************************************
  Amortized analysis for Append in DynaArrayList
******************************************************************************/

module AppendAmortDAL {
  
  import opened TypeR0
  import opened DynaArrayList
  import opened LemDynaArrayList

  // Cost of append
  ghost function T(N:nat, C:nat, m:nat) : R0
    requires N <= C
  {
    if N < C then Tappend2(N)    // = 1
             else Tappend(m, N)  // = (m+1)*N + 1
  }

  // Cost sequence: cost at the state immediately before the i-th append:
  ghost function c(i:nat, N:nat, C:nat, m:nat) : R0
    requires N <= C
  {
    1.0 // TODO
  }

  // Cost over a sequence of n appends
  method costSequence<T(0)>(al:DynaArrayList<T>, n:nat) returns (t:R0)
    modifies al.Repr()
    requires al.Valid()
    requires n > 0
    ensures al.Valid() && fresh(al.Repr() - old(al.Repr())) 
  {
    t := 0.0; 

    for i := 1 to n+1
      modifies al.Repr()
      invariant al.Valid() && fresh(al.Repr() - old(al.Repr())) 
    {
      var N, m, C := al.Size(), al.m, al.Capacity();
    label before:
      var x:T :| true;
      var t := al.Append(x);
      assert t == if old@before(al.IsFull()) then Tappend(m, N) else Tappend2(N);
      assert t == T(N, C, m);
      
      t := t + t;
    }
  }

}