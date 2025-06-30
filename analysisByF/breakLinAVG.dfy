include "../theory/math/SummationReal.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"

import opened SummationReal
import opened TypeR0
import opened ComplexityR0

ghost function T(N:nat, i:nat) : nat
  requires 0 <= i < N
{
  i+1
}

ghost method breakLinAVG(N:nat, P:nat->bool)
  returns (t:nat)
  requires N > 0
  requires exists i :: 0 <= i < N && P(i)
  ensures  exists k :: 0 <= k < N && P(k) && t == T(N,k)
{
  var i;
  i, t := 0, 1;
  while i != N && !P(i) 
    invariant 0 <= i <= N
    invariant forall j :: 0 <= j < i ==> !P(j)
    invariant exists k :: i <= k < N && P(k)
    invariant t == i+1
    decreases N - i
  {
    i := i + 1;
    t := t + 1;
  }
  assert P(i) && t == T(N,i);
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
    // Run the algorithm in scenario where P(p) holds
    var pred := inputScenario(N, p); 
    ghost var t := breakLinAVG(N, pred); 
    assert exists k :: 0 <= k < N && pred(k) && t == k+1;
    assert t == T(N,p);
    
    // Add weighted contribution to expectation
    lem_sumr_dropLastAll(0, p-1);
    tE := tE + t as real * probability(N,pred,p);
    p  := p + 1;
  }
  assert tE == sumr(0, N-1, i => (i+1) as real * (1.0 / N as real)); 
  assert tE == Tavg(N) by { lem_solveSum(N); }

  assert bigOR0(Tavg, n => n as R0) by { var c, n0 := lem_TavgBigOR0lin(); }
}

ghost function probability(N:nat, pred:nat->bool, p:nat) : R0
  requires 0 <= p < N
  requires pred(p) && forall k :: 0 <= k < N && pred(k) ==> k == p
{
  1.0 / N as R0
}

ghost method inputScenario(N:nat, p:nat) returns (pred0:nat->bool)
  requires N > 0
  requires 0 <= p < N
  ensures pred0(p)
  ensures forall k :: 0 <= k < N && pred0(k) ==> k == p
{
  assume {:axiom} exists pred:nat->bool :: pred(p) && forall k :: 0 <= k < N && pred(k) ==> k == p;
  pred0 :| pred0(p) && forall k :: 0 <= k < N && pred0(k) ==> k == p;
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
    == { assert forall k:int :: 1<=k<=N ==> 
           (i => ((i-1)+1) as real)(k) == (i => i as real)(k);
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