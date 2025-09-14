include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/Log2Nat.dfy"
include "../../../theory/math/Log2Real.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity.dfy"

import opened LemFunction
import Nat = Log2Nat
import opened Log2Real
import opened TypeR0
import opened Complexity

type Input {
  function size() : nat
}

ghost function f(n:nat) : nat
{
  if n>0 then Nat.log2(n) else 0
}

method log(x:Input) returns (ghost t:nat)
  ensures t <= f(x.size())
  ensures tIsBigO(x.size(), t as R0, log2Growth())
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
  assert liftToR0(f) in O(log2Growth()) by { var c, n0 := lem_fBigOlog2(); }
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
lemma lem_TclosedBound(n:nat)
  decreases n
  ensures n==0 ==> T(n) == 0
  ensures n>0  ==> T(n) <= Nat.log2(n)
{  
  if n > 1 {
    reveal Nat.log2(); 
    lem_TclosedBound(n/2);
  } 
}

lemma lem_fBigOlog2() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOfrom(c, n0, liftToR0(f), log2Growth())
{
  c, n0 := 1.0, 1;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) as R0 <= c*log2Growth()(n)
  {
    calc {
         f(n) as R0;
      == (if n>0 then Nat.log2(n) else 0) as R0;
      == Nat.log2(n) as R0;
      <= { lem_log2_NatLowBound(n);  }
         log2(n as R0);  
      == c*log2Growth()(n); 
    }
  }
}

//**************************************************************************//

ghost method testT1() {
  reveal Nat.log2();
  var N:nat := 1;
  var r := T(N);
  assert r == 0; 
  assert r <= Nat.log2(N+1); 

  N := 2;
  r := T(N);
  assert r == 1;
  assert r <= Nat.log2(N+1);

  N := 3;
  r := T(N); 
  assert r == 1;
  assert r <= Nat.log2(N+1);

  N := 4;
  r := T(N); 
  assert r == 2;
  assert r <= Nat.log2(N+1);

  N := 5;
  r := T(N); 
  assert r == 2;
  assert r <= Nat.log2(N+1);

  N := 10;
  r := T(N); 
  assert r == 3;
  assert r <= Nat.log2(N+1);  

  N := 40;
  r := T(N); 
  assert r == 5;
  assert r <= Nat.log2(N+1);    
} 