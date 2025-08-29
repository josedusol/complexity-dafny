include "../../../theory/ComplexityNat.dfy"
include "../../../theory/LemComplexityNat.dfy"

import opened ComplexityNat
import opened LemComplexityNat

type Input {
  function size() : nat
}

ghost function f(N:nat) : nat
{
  1
}

method breakConstBT(x:Input, P:nat->bool) returns (ghost t:nat)
  ensures t <= f(x.size()) 
  ensures tIsBigO(x.size(), t, constGrowth())
{
  var N := x.size();
  assume {:axiom} N > 0 ==> P(0);  // best case
  var i;
  i, t := 0, 0;
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
  assert f in O(constGrowth()) by { lem_bigO_constGrowth(f, 1); }
} 