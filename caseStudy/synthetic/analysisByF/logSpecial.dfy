include "../../../theory/math/Log2Nat.dfy"

import opened Log2Nat

// Instanciamos las definiciones de complejidad para log2 con n>0

ghost predicate tIsBigOLog(n:nat, t:nat)
{ 
  exists f:nat -> nat :: t <= f(n) && bigOLog(f)
}

ghost predicate bigOLog(f:nat->nat) 
{ 
  exists c:nat, n0:nat :: bigOLogfrom(c, n0, f)
}

ghost predicate bigOLogfrom(c:nat, n0:nat, f:nat->nat)
{
  forall n:nat :: 1 <= n0 <= n ==> f(n) <= c*log2(n)  
}

//**************************************************************************//

type Input {
  function size() : nat
}

ghost function f(N:nat) : nat
{
  log2(N+1) 
}

method log(x:Input) returns (ghost t:nat)
  requires x.size() > 0
  ensures  t <= f(x.size())
  ensures  tIsBigOLog(x.size(), t)
{
  var N := x.size();
  t := 0;

  var i := N;
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
  assert t <= log2(N) by { lem_TclosedBound(N); }
  assert t <= f(N)    by { lem_log2_MonoIncr(N, N+1); }
  assert bigOLog(f) by { var c, n0 := lem_fBigOlog(); }
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
  requires 1 <= N
  decreases N
  ensures T(N) <= log2(N)
{  
  if N > 1 {
    reveal log2(); 
    lem_TclosedBound(N/2);
  } 
}

lemma lem_fBigOlog() returns (c:nat, n0:nat)
  ensures c > 0 && bigOLogfrom(c, n0, f)
{
  c, n0 := 2, 2;
  forall n:nat | 1 <= n0 <= n
    ensures f(n) <= c*log2(n)
  {
    calc {
         f(n);
      == log2(n+1);
      <= { assert n>=1; lem_log2_MonoIncr(n+1, 2*n); }
         log2(2*n);  
      == { reveal log2(); }
         log2(2) + log2(n);             
      == { reveal log2(); }
         1+log2(n);    
    }
    assert n >= 0 ==> f(n) <= 1+log2(n);
    assert n >= n0 ==> f(n) <= c*log2(n) by { reveal log2(); } 
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