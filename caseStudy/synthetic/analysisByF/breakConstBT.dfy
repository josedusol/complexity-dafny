include "../../../theory/math/Function.dfy"
include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity/Asymptotics.dfy"
include "../../../theory/Complexity/LemBigOh.dfy"

import opened Function
import opened LemFunction
import opened TypeR0
import opened Asymptotics
import opened LemBigOh

type Input {
  function size() : nat
}

ghost function f(n:nat) : nat
{
  1
}

method breakConstBT(x:Input, P:nat->bool) returns (ghost t:nat)
  ensures t <= f(x.size()) 
  ensures tIsBigOh(x.size(), t as R0, constGrowth())
{
  var N := x.size();
  t := 0;
  assume {:axiom} N > 0 ==> P(0);  // best case
  
  var i := 0;
  while i != N
    invariant 0 <= i <= N
    invariant (i == 0 && t == 0) || (i == N && t == 1)
    decreases N - i
  {
    if !P(i) {  // Op. interesante
      i := i+1 ;    
    } else {
      i := N;  // break;
    }
    t := t+1 ;
  }

  assert t <= f(N);
  assert liftToR0(f) in O(constGrowth()) by { 
    lem_ConstGrowth(n => 1 as R0, 1.0);
    lem_Exten(liftToR0(f), n => 1 as R0)
      by { assert 1 as R0 == 1.0; } 
  }
} 