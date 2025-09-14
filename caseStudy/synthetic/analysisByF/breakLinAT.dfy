include "../../../theory/math/SumReal.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity.dfy"

import opened SumReal
import opened TypeR0
import opened Complexity

type Input {
  function size() : nat
}

ghost function T(N:nat, i:nat) : nat
  requires 0 <= i < N
{
  i+1
}

ghost method breakLinAT(x:Input, P:nat->bool) returns (t:nat)
  requires x.size() > 0
  requires exists i :: 0 <= i < x.size() && P(i)
  ensures  exists k :: 0 <= k < x.size() && P(k) && t == T(x.size(),k)
{
  var N := x.size();
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
  ensures tIsBigO(N, tE, linGrowth())
{
  tE := 0.0; 
  var p := 0; reveal sum();  
  while p < N
    invariant 0 <= p <= N
    invariant tE == sum(0, p-1, i => (i+1) as real * (1.0 / N as real))
    decreases N - p
  {
    // Run the algorithm in scenario where P(p) holds
    var x, pred := inputScenario(N, p); 
    ghost var t := breakLinAT(x, pred); 
    assert exists k :: 0 <= k < N && pred(k) && t == k+1;
    assert t == T(N,p);
    
    // Add weighted contribution to expectation
    lem_sum_DropLastAuto(0, p-1);
    tE := tE + t as real * probability(N,pred,p);
    p  := p + 1;
  }
  assert tE == sum(0, N-1, i => (i+1) as real * (1.0 / N as real)); 
  assert tE == Tavg(N) by { lem_solveSum(N); }
  assert Tavg in O(linGrowth()) by { var c, n0 := lem_TavgBigOlin(); }
}

ghost function probability(N:nat, pred:nat->bool, p:nat) : R0
  requires 0 <= p < N
  requires pred(p) && forall k :: 0 <= k < N && pred(k) ==> k == p
{
  1.0 / N as R0
}

ghost method inputScenario(N:nat, p:nat) returns (x:Input, pred0:nat->bool)
  requires N > 0
  requires 0 <= p < N
  ensures pred0(p)
  ensures x.size() == N
  ensures forall k :: 0 <= k < N && pred0(k) ==> k == p
{
  assume {:axiom} exists x:Input :: x.size() == N;
  x :| x.size() == N;
  assume {:axiom} exists pred:nat->bool :: pred(p) && forall k :: 0 <= k < N && pred(k) ==> k == p;
  pred0 :| pred0(p) && forall k :: 0 <= k < N && pred0(k) ==> k == p;
}

lemma lem_solveSum(N:nat)
  requires N > 0
  ensures Tavg(N) == sum(0, N-1, i => (i+1) as real * (1.0 / N as real))
{ 
  var c:real := 1.0 / N as real; 
  calc {
       sum(0, N-1, i => (i+1) as real * c);
    == { assert forall k:int :: 0<=k<=N-1 ==>   
           (i => (i+1) as real * c)(k) == (l => c*(i => (i+1) as real)(l))(k);
         lem_sum_Leibniz(0, N-1, i => (i+1) as real * c, 
                                 l => c*(i => (i+1) as real)(l)); }
       sum(0, N-1, l => c*(i => (i+1) as real)(l));
    == { lem_sum_LinearityConst(0, N-1, c, i => (i+1) as real); }
       c * sum(0, N-1, i => (i+1) as real);
    == { lem_sum_ShiftIndex(0, N-1, 1, i => (i+1) as real); }
       c * sum(1, N, i => (i => (i+1) as real)(i-1));
    == { assert forall k:int :: 1<=k<=N ==> 
           (i => ((i-1)+1) as real)(k) == (i => i as real)(k);
         lem_sum_Leibniz(1, N, i => (i => (i+1) as real)(i-1), i => i as real); }
       c * sum(1, N, i => i as real);
    == { lem_sum_Interval(1, N); }
       c * ((N*(N+1) + 1*(1-1)) as real / 2.0);
    == c * ((N*(N+1)) as real / 2.0);  
    == (1.0 / N as real) * ((N*(N+1)) as real / 2.0); 
    == (N + 1) as real / 2.0;
  }
} 

lemma lem_TavgBigOlin() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOfrom(c, n0, Tavg, linGrowth())
{
  c, n0 := 1.0, 1;
  forall n:nat | 0 <= n0 <= n
    ensures Tavg(n) <= c*linGrowth()(n)
  {
    calc {
         Tavg(n);
      == (n + 1) as R0 / 2.0; 
      <= c * n as R0;
      == c*linGrowth()(n);
    }
  }
}