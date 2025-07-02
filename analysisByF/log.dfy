include "../theory/math/LogNat.dfy"
include "../theory/ComplexityNat.dfy"

import opened LogNat
import opened ComplexityNat

ghost function f(N:nat) : nat
{
  if N>0 then log2(N) else 0
}

method log(N:nat)
  returns (ghost t:nat)
  ensures t <= f(N)
  ensures tIsBigO(N, t, logGrowth())
{
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
 
  assert bigO(f, logGrowth()) by { var c, n0 := lem_fBigOlog(); }
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

lemma lem_fBigOlog() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f, logGrowth())
{
  // we show that c=1 and n0=1
  c, n0 := 1, 1;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*logGrowth()(n)
  {
    assert f(n) <= c*logGrowth()(n); 
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