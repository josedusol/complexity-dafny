include "../../../theory/math/Function.dfy"
include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity/Asymptotics.dfy"

import opened Function
import opened LemFunction
import opened TypeR0
import opened Asymptotics

type Input {
  function size() : nat
}

ghost function f(n:nat) : nat
{
  (n*(n+1))/2
}

method quadTriangle(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigOh(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0;

  var i, j := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T1(N,0) - T1(N,i) // = T1(N, N-i)
    decreases N - i
  {
    j := i; ghost var t' := 0; 
    while j != N
      invariant i <= j <= N && i != N
      invariant t' == T2(N,i) - T2(N,j)  // = T2(N, (N-j)+i)
      decreases N - j
    {
      // Op. interesante
      j  := j+1;
      t' := t'+1;
    }
    lem_T2reverseIndex(N, i); 
    i := i+1;
    t := t+t';
  }

  assert t == T1(N, 0); 
  assert t == f(N) by { lem_T1closed(N, 0); }
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }  
} 

method quadTriangleFor(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigOh(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0;

  for i := 0 to N
    invariant t == T1(N,0) - T1(N,i) // = T1(N, N-i)
  {
    ghost var t' := 0;
    for j := i to N
      invariant t' == T2(N,i) - T2(N,j)  // = T2(N, (N-j)+i)
    {
      // Op. interesante
      t' := t'+1;
    }
    t := t+t';
  }
  
  assert t == T1(N, 0); 
  assert t == f(N) by { lem_T1closed(N, 0); }
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); } 
}

ghost function T1(N:nat, i:int): nat
  requires  0 <= i <= N
  decreases N - i
{
  if i != N 
  then T1(N, i+1) + T2(N, i)
  else 0
}

ghost function T2(N:nat, j:int): nat
  requires  0 <= j <= N
  decreases N - j
{
  if j != N 
  then T2(N, j+1) + 1 
  else 0
}

lemma lem_T2closed(N:nat, j:int)
  requires 0 <= j <= N
  decreases N - j
  ensures T2(N, j) == N - j
{
  if j != N  {
    lem_T2closed(N, j+1);
  }
}

lemma {:axiom} lem_T2reverseIndex(N:nat, i:int)
  requires 0 <= i < N
  ensures T2(N, i) == T2(N, N-(i+1))
// Esto es esencialmente lem_RevIndex
// pero en forma de recurrencia

lemma lem_T1closed(N:nat, i:nat)
  requires 0 <= i <= N
  decreases N - i
  ensures T1(N, i) == ((N-i)*((N-i)+1))/2
{ 
  if i != N {
    lem_T2closed(N, i);
    lem_T1closed(N, i+1);
  }    
} 

lemma lem_fBigOquad() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOhFrom(c, n0, liftToR0(f), quadGrowth())
{
  c, n0 := 1.0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) as R0 <= c*quadGrowth()(n)
  {
    calc {
         f(n) as R0;
      == ((n*(n+1))/2) as R0; 
      <= { assert (n*(n+1))/2 <= n*n; }
         (n*n) as R0;   
      <= c * (n*n) as R0;
      == c*quadGrowth()(n);
    }
  }
}

//**************************************************************************//

ghost method testT2() {
  var N := 4; 
  var i := 0; 
  var r := T2(N, i);
  assert r == 4; 
  assert N - i == 4;

  i := 1; 
  r := T2(N, i);
  assert r == 3;
  assert N - i == 3;

  i := 2; 
  r := T2(N, i);
  assert r == 2;
  assert N - i == 2;  

  i := 3; 
  r := T2(N, i);
  assert r == 1;
  assert N - i == 1; 

  i := 4; 
  r := T2(N, i);
  assert r == 0;
  assert N - i == 0;    
}  

ghost method testT1() {
  var N:nat := 0;
  var r := T1(N, 0);
  assert r == 0; 
  assert (N*(N+1))/2 == 0; 

  N := 1;
  r := T1(N, 0);
  assert r == 1;
  assert (N*(N+1))/2 == 1;

  N := 2;
  r := T1(N, 0); 
  assert r == 3;
  assert (N*(N+1))/2 == 3;

  N := 3;
  r := T1(N, 0); 
  assert r == 6;
  assert (N*(N+1))/2 == 6;

  N := 4;
  r := T1(N, 0); 
  assert r == 10;
  assert (N*(N+1))/2 == 10;
}