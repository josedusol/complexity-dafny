include "../theory/math/SummationReal.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"

import opened SummationReal
import opened TypeR0
import opened ComplexityR0

predicate inv(s:seq<int>, x:int, i:nat, N:int)
{
     0 <= i <= N && N <= |s|
  && (0 <= N < |s| ==> s[i] == x)      
  && (N == |s|     ==> (forall j :: 0 <= j < i ==> s[j] != x))
}

predicate post(s:seq<int>, x:int, i:nat)
{
     (0 <= i < |s| ==> s[i] == x)
  && (i == |s|     ==> (forall j :: 0 <= j < |s| ==> s[j] != x))
}

ghost function T(s:seq<int>, x:int, i:nat) : nat
  requires 0 <= i < |s|
  requires s[i] == x
{
  i+1
}

ghost method linearSearch(s:seq<int>, x:int)
  returns (i:nat, t:nat)
  requires x in s
  ensures  post(s, x, i)
  ensures  exists k :: 0 <= k < |s| && s[k] == x && t == T(s, x, k)
{
  var N;
  i, N, t := 0, |s|, 1;
  while i != N && s[i] != x
    invariant inv(s, x, i, N)
    invariant forall j :: 0 <= j < i ==> s[j] != x
    invariant exists k :: i <= k < |s| && s[k] == x
    invariant t == i+1
    decreases N - i
  {
    i := i + 1;
    t := t + 1;
  }
  assert s[i] == x && t == T(s,x,i);
} 
 

ghost function Tavg(N:nat) : R0
{
  (N + 1) as real / 2.0
}

ghost method expectationLoop(N:nat)
  returns (tE:real)
  requires N > 0
  ensures tE == Tavg(N)
  ensures tIsBigOR0(N, tE, n => n as R0)
{
  tE := 0.0; 
  var p := 0; reveal sumr();  
  while p < N
    invariant 0 <= p <= N
    invariant tE == sumr(0, p-1, i => (i+1) as real * (1.0 / N as real))
    decreases N - p
  {
    // Run algorithm in scenario where s[p] == x
    var s, x := inputScenario(N, p); 
    var _, t := linearSearch(s, x); 
    assert exists k :: 0 <= k < |s| && s[k] == x && t == k+1;
    assert t == T(s,x,p);
    
    // Add weighted contribution to expectation
    lem_sumr_dropLastAll(0, p-1);
    tE := tE + t as real * probability(s,x,p);
    p  := p + 1;
  }
  assert tE == sumr(0, N-1, i => (i+1) as real * (1.0 / N as real)); 
  assert tE == Tavg(N) by { lem_solveSum(N); }

  assert bigOR0(Tavg, n => n as R0) by { var c, n0 := lem_TavgBigOR0lin(); }
}

ghost function probability(s:seq<int>, x:int, p:nat) : R0
  requires 0 <= p < |s|
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  requires s[p] == x
{
  1.0 / |s| as R0
}

ghost method inputScenario(N:nat, p:nat) returns (s0:seq<int>, x0:int)
  requires N > 0
  requires 0 <= p < N
  ensures  |s0| == N
  ensures  forall i, j :: 0 <= i < j < |s0| ==> s0[i] != s0[j]
  ensures  s0[p] == x0
{
  assume {:axiom} 
    exists s:seq<int> :: |s| == N && (forall i, j :: 0 <= i < j < N ==> s[i] != s[j]);
  s0 :| |s0| == N && forall i, j :: 0 <= i < j < N ==> s0[i] != s0[j];
  assume {:axiom} 
    exists x:int :: s0[p] == x;
  x0 :| s0[p] == x0;
}

lemma lem_solveSum(N:nat)
  requires N > 0
  ensures Tavg(N) == sumr(0, N-1, i => (i+1) as real * (1.0 / N as real))
{ 
  var c:real := 1.0 / N as real; 
  calc {
       sumr(0, N-1, i => (i+1) as real * c);
    == { assert forall k:int :: 0<=k<=N-1 ==>   
          (i => (i+1) as real * c)(k) == (l => c*(i => (i+1) as real)(l))(k);
         lem_sumr_leibniz(0, N-1, i => (i+1) as real * c, 
                                  l => c*(i => (i+1) as real)(l)); }
       sumr(0, N-1, l => c*(i => (i+1) as real)(l));
    == { lem_sumr_linearityConst(0, N-1, c, i => (i+1) as real); }
       c * sumr(0, N-1, i => (i+1) as real);
    == { lem_sumr_shiftIndex(0, N-1, 1, i => (i+1) as real); }
       c * sumr(1, N, i => (i => (i+1) as real)(i-1));
    == { assert forall k:int :: 1<=k<=N ==> (i => ((i-1)+1) as real)(k) == (i => i as real)(k);
         lem_sumr_leibniz(1, N, i => (i => (i+1) as real)(i-1), i => i as real); }
       c * sumr(1, N, i => i as real);
    == { lem_sumr_interval(1, N); }
       c * ((N*(N+1) + 1*(1-1)) as real / 2.0);
    == c * ((N*(N+1)) as real / 2.0);  
    == (1.0 / N as real) * ((N*(N+1)) as real / 2.0); 
    == (N + 1) as real / 2.0;
  }
} 

lemma lem_TavgBigOR0lin() returns (c:R0, n0:nat)
  ensures bigOR0from(c, n0, Tavg, n => n as R0)
{
  // we show that c=1 and n0=1
  c, n0 := 1.0, 1;
  forall n:nat | 0 <= n0 <= n
    ensures Tavg(n) <= c*(n => n as R0)(n)
  {
    calc {
         Tavg(n);
      == (n + 1) as real / 2.0;
      <= n as real;
    }
    assert Tavg(n) <= c*(n => n as R0)(n); 
  }
}