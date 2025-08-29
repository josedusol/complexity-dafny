include "../../../theory/math/Log2Nat.dfy"
include "../../../theory/ComplexityNat.dfy"

import opened Log2Nat
import opened ComplexityNat

type Input {
  function size() : nat
}

ghost function f(N:nat) : nat
{
  if N>0 then log2(N) else 0
}

method log(x:Input) returns (ghost t:nat)
  ensures t <= f(x.size())
  ensures tIsBigO(x.size(), t, log2Growth())
{
  var N := x.size();
  var i;
  i, t := N, 0;
  while i > 1
    invariant 0 <= i <= N
    invariant t == T(N) - T(i)
    decreases i
  {
    // Op. interesante
    i := i/2 ;
    t := t+1 ;
  }
  assert t == T(N); 
  assert t <= f(N) by { lem_TclosedBound(N); }
 
  assert f in O(log2Growth()) by { var c, n0 := lem_fBigOlog2(); }
} 

ghost function T(i:nat) : nat
  requires 0 <= i 
  decreases i
{
  if i > 1
  then T(i/2) + 1 
  else 0
}

// T(N) ~ log2(N)
// T(N) = Θ(log(N)) 
lemma lem_TclosedBound(N:nat)
  decreases N
  ensures N==0 ==> T(N) == 0
  ensures N>0  ==> T(N) <= log2(N)
{  
  if N > 1 {
    reveal log2(); 
    lem_TclosedBound(N/2);
  } 
}

lemma lem_fBigOlog2() returns (c:nat, n0:nat)
  ensures c > 0 && bigOfrom(c, n0, f, log2Growth())
{
  c, n0 := 1, 1;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*log2Growth()(n)
  {
    assert f(n) <= c*log2Growth()(n); 
  }
}

//**************************************************************************//

ghost method testT1() {
  reveal log2();
  var N:nat := 1;
  var r := T(N);
  assert r == 0; 
  assert r <= log2(N+1); 

  N := 2;
  r := T(N);
  assert r == 1;
  assert r <= log2(N+1);

  N := 3;
  r := T(N); 
  assert r == 1;
  assert r <= log2(N+1);

  N := 4;
  r := T(N); 
  assert r == 2;
  assert r <= log2(N+1);

  N := 5;
  r := T(N); 
  assert r == 2;
  assert r <= log2(N+1);

  N := 10;
  r := T(N); 
  assert r == 3;
  assert r <= log2(N+1);  

  N := 40;
  r := T(N); 
  assert r == 5;
  assert r <= log2(N+1);    
} 