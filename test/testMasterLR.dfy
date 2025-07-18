include "../theory/math/ExpNat.dfy"
include "../theory/math/ExpReal.dfy"
include "../theory/math/LemBoundsNat.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/LogNat.dfy"
include "../theory/math/SumInt.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"
include "../theory/MasterLR.dfy"

import Nat = ExpNat
import opened ExpReal
import opened LemBoundsNat
import opened LemFunction
import opened LogNat 
import opened TypeR0
import opened ComplexityR0
import opened MasterLR

// Recurrence:
//   T1(n) = / 0             , n <= 1
//           \ T1(n-1) + 1   , n > 1 
opaque ghost function T1(n:nat) : nat
  decreases n 
{   
  if n <= 1
  then 0  
  else T1(n-1) + 1  
} 

lemma lem_T1def(n:nat)
  ensures n <= 1 ==> T1(n) == 0
  ensures n > 1  ==> T1(n) == 1*T1(n-1) + 1
{
  reveal T1();
}

// Exact closed form:
//   T1(n) = n-1
// Asymptotic closed form:
//   T1(n) in O(n)
lemma test_masterMethodForT1lifted()
  ensures bigO(liftToR0(T1), n => exp(n as R0, 1.0))
{
  var a:nat       := 1;
  var b:nat       := 1;
  var c:R0        := 0.0;
  var k:R0        := 0.0;
  var T1':nat->R0 := liftToR0(T1);
  var w:nat->R0   := liftToR0(n => 1);

  forall n:nat 
    ensures T1'(n) == TbodyLR2(a, b, c, T1', w, n)
  {
    reveal TbodyLR2;
    lem_T1def(n);
  }     
  assert bigO(w, n => exp(n as R0, k)) by {   
    // we show that c=1 and n0=1
    forall n:nat 
      ensures 0 <= 1 <= n ==> w(n) <= 1.0*polyGrowth(k)(n)
    {
      if 0 <= 1 <= n {
        assert exp(n as R0, k) == 1.0 by { lem_expZeroAll(); }
        assert w(n) <= 1.0*polyGrowth(k)(n); 
      }
    }
    assert bigOfrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR2(a, b, c, T1', w, k);
}   

//**************************************************************************//

// Recurrence:
//   T2(n) = / 0             , n <= 2
//           \ T2(n-2) + 1   , n > 2
opaque ghost function T2(n:nat) : nat
  decreases n
{
  if n <= 2
  then 0  
  else T2(n-2) + 1 
}

lemma lem_T2def(n:nat)
  ensures n <= 2 ==> T2(n) == 0
  ensures n > 2  ==> T2(n) == 1*T2(n-2) + 1
{
  reveal T2();
}

// Exact closed form:
//   T2(n) = 1/4*(2*n - (-1)^n - (-1)^(2 n) - 2)
// Asymptotic closed form:
//   T2(n) in O(n)
lemma test_masterMethodForT2lifted()
  ensures bigO(liftToR0(T2), n => exp(n as R0, 1.0))
{
  var a:nat       := 1;
  var b:nat       := 2;
  var c:R0        := 0.0;
  var k:R0        := 0.0;
  var T2':nat->R0 := liftToR0(T2);
  var w:nat->R0   := liftToR0(n => 1);

  forall n:nat 
    ensures T2'(n) == TbodyLR2(a, b, c, T2', w, n)
  {
    reveal TbodyLR2;
    lem_T2def(n);
  } 
  assert bigO(w, n => exp(n as R0, k)) by {  // k=0
    // we show that c=1 and n0=1
    forall n:nat 
      ensures 0 <= 1 <= n ==> w(n) <= 1.0*polyGrowth(k)(n)
    {
      if 0 <= 1 <= n {
        assert polyGrowth(k)(n) == 1.0 by { lem_expZeroAll(); }
        assert 1.0 <= 1.0*polyGrowth(k)(n); 
      }
    }
    assert bigOfrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR2(a, b, c, T2', w, k); 
  assert bigO(T2', (n:nat) => exp(n as R0, 1.0));
} 

//**************************************************************************//

// Recurrence:
//   T3(n) = / 5             , n <= 2
//           \ T3(n-2) + 4   , n > 2
opaque ghost function T3(n:nat) : nat
  decreases n
{
  if n <= 2
  then 5  
  else T3(n-2) + 4 
}

lemma lem_T3def(n:nat)
  ensures n <= 2 ==> T3(n) == 5
  ensures n > 2  ==> T3(n) == 1*T3(n-2) + 4
{
  reveal T3();
}

// Exact closed form:
//   T3(n) = 2*n - (-1)^n - (-1)^(2*n) + 3
// Asymptotic closed form:
//   T3(n) in O(n)
lemma test_masterMethodForT3lifted()
  ensures bigO(liftToR0(T3), n => exp(n as R0, 1.0))
{ 
  var a:nat       := 1;
  var b:nat       := 2;
  var c:R0        := 5.0;
  var k:R0        := 0.0;
  var T3':nat->R0 := liftToR0(T3);
  var w:nat->R0   := liftToR0(n => 4);

  forall n:nat 
    ensures T3'(n) == TbodyLR2(a, b, c, T3', w, n)
  {
    reveal TbodyLR2;
    lem_T3def(n);
  } 
  assert bigO(w, n => exp(n as R0, k)) by {
    // we show that c=4 and n0=1
    forall n:nat 
      ensures 0 <= 1 <= n ==> w(n) <= 4.0*polyGrowth(k)(n)
    {
      if 0 <= 1 <= n {
        assert polyGrowth(k)(n) == 1.0 by { lem_expZeroAll(); }
        assert w(n) <= 4.0*polyGrowth(k)(n); 
      }
    }
    assert bigOfrom(4.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR2(a, b, c, T3', w, k);
  assert bigO(T3', n => exp(n as R0, 1.0));
} 

//**************************************************************************//

// Recurrence:
//   T4(n) = / 0               , n <= 1
//           \ 2*T4(n-1) + 1   , n > 1
opaque ghost function T4(n:nat) : nat
  decreases n
{
  if n <= 1
  then 0  
  else 2*T4(n-1) + 1 
}

lemma lem_T4def(n:nat)
  ensures n <= 1 ==> T4(n) == 0
  ensures n > 1  ==> T4(n) == 2*T4(n-1) + 1
{
  reveal T4();
}

// Exact closed form:
//   T4(n) = 2^(n-1) - 1
// Asymptotic closed form:
//   T4(n) in O(2^n)
lemma test_masterMethodForT4lifted()
  ensures bigO(liftToR0(T4), (n:nat) => exp(n as R0, 0.0)*exp(2.0, (n/1) as R0))
{ 
  var a:nat       := 2;
  var b:nat       := 1;
  var c:R0        := 0.0;
  var k:R0        := 0.0;
  var T4':nat->R0 := liftToR0(T4);
  var w:nat->R0   := liftToR0(n => 1);
  var g:nat->R0   := (n:nat) => exp(n as R0, 0.0)*exp(2.0, (n/1) as R0);

  forall n:nat 
    ensures T4'(n) == TbodyLR2(a, b, c, T4', w, n)
  {
    reveal TbodyLR2;
    lem_T4def(n);
  } 
  assert bigO(w, n => exp(n as R0, k)) by {
    // we show that c=1 and n0=1
    forall n:nat 
      ensures 0 <= 1 <= n ==> w(n) <= 1.0*polyGrowth(k)(n)
    {
      if 0 <= 1 <= n {
        assert polyGrowth(k)(n) == 1.0 by { lem_expZeroAll(); }
        assert w(n) <= 1.0*polyGrowth(k)(n); 
      }
    }
    assert bigOfrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR2(a, b, c, T4', w, k);
  assert bigO(T4', (n:nat) => exp(n as R0, 0.0)*exp(2.0, (n/1) as R0));
}  

//**************************************************************************//

// Recurrence:
//   T5(n) = / 0                 , n <= 1
//           \ 2*T5(n-1) + 3*n   , n > 1
opaque ghost function T5(n:nat) : nat
  decreases n
{
  if n <= 1
  then 0  
  else 2*T5(n-1) + 3*n 
}

lemma lem_T5def(n:nat)
  ensures n <= 1 ==> T5(n) == 0
  ensures n > 1  ==> T5(n) == 2*T5(n-1) + 3*n 
{
  reveal T5();
}

// Exact closed form:
//   T5(n) = 9*2^(n-1) - 3*n - 6
// Asymptotic closed form by MT: 
//   T5(n) in O(n*2^n)
// Thiger bound:
//   T5(n) ∈ Θ(2^n)
lemma test_masterMethodForT5lifted() 
  ensures bigO(liftToR0(T5), n => (n as R0)*exp(2.0, n as R0))
{ 
  var a:nat       := 2;
  var b:nat       := 1;
  var c:R0        := 0.0;
  var k:R0        := 1.0;
  var T5':nat->R0 := liftToR0(T5);
  var w:nat->R0   := liftToR0(n => 3*n);
 
  forall n:nat 
    ensures T5'(n) == TbodyLR2(a, b, c, T5', w, n)
  {
    reveal TbodyLR2;
    lem_T5def(n);
  } 
  assert bigO(w, n => exp(n as R0, k)) by { 
    // we show that c=3 and n0=1
    forall n:nat 
      ensures 0 <= 1 <= n ==> w(n) <= 3.0*exp(n as R0, k)
    {
      if 0 <= 1 <= n {
        assert exp(n as R0, k) == n as R0 by { lem_expOneAll(); } 
        assert w(n) <= 3.0*exp(n as R0, k); 
      }
    }
    assert bigOfrom(3.0, 1, w, n => exp(n as R0, k));
  } 
  thm_masterMethodLR2(a, b, c, T5', w, k);
  test_masterMethodForT5lifted_simplify();
}  

lemma test_masterMethodForT5lifted_simplify() 
  requires bigO(liftToR0(T5), (n:nat) => exp(n as R0, 1.0)*exp(2.0 as R0, (n/1) as R0))
  ensures  bigO(liftToR0(T5), (n:nat) => (n as R0)*exp(2.0, n as R0))
{
  var T5':nat->R0 := liftToR0(T5);
  var c:R0, n0:nat :| bigOfrom(c, n0, T5', (n:nat) => exp(n as R0, 1.0)*exp(2.0, (n/1) as R0));
  assert forall n:nat :: 0 <= n0 <= n   ==> T5'(n) <= c*exp(n as R0, 1.0)*exp(2.0, (n/1) as R0);
  assert forall n:nat :: 0 <= n0+1 <= n ==> T5'(n) <= c*exp(n as R0, 1.0)*exp(2.0, (n/1) as R0);
  lem_expOneAll();
  assert forall n:nat :: 0 <= n0+1 <= n ==> T5'(n) <= c*(n as R0)*exp(2.0, (n/1) as R0);
  assert forall n:nat :: 0 <= n0+1 <= n ==> T5'(n) <= c*(n as R0)*exp(2.0, n as R0);
  assert bigOfrom(c, n0+1, T5', (n:nat) => (n as R0)*exp(2.0, n as R0)); 
}

//**************************************************************************//

// Recurrence:
//   T6(n) = / 0                   , n <= 2
//           \ 2*T6(n-2) + 3*n^2   , n > 2
opaque ghost function T6(n:nat) : nat
  decreases n
{
  if n <= 2
  then 0   
  else 2*T6(n-2) + 3*Nat.exp(n,2)
}

lemma lem_T6def(n:nat)
  ensures n <= 2 ==> T6(n) == 0
  ensures n > 2  ==> T6(n) == 2*T6(n-2) + 3*Nat.exp(n,2) 
{
  reveal T6();
}

// Exact closed form:
//   T6(n) = ... hard
// Asymptotic closed form by MT:
//   T6(n) ∈ O(n^2*2^(n/2))
// Thiger bound:
//   T7(n) ∈ Θ(2^(n/2)) 
lemma test_masterMethodForT6() 
  ensures bigO(liftToR0(T6), n => ((n*n) as R0)*exp(2.0, (n/2) as R0))
{ 
  var a:nat       := 2;
  var b:nat       := 2;
  var c:R0        := 0.0;
  var k:R0        := 2.0;
  var T6':nat->R0 := liftToR0(T6);
  var w:nat->R0   := liftToR0(n => 3*Nat.exp(n,2));

  forall n:nat 
    ensures T6'(n) == TbodyLR2(a, b, c, T6', w, n)
  {
    reveal TbodyLR2;
    lem_T6def(n);
  } 
  assert bigO(w, n => exp(n as R0, k)) by {
    // we show that c=3 and n0=1
    forall n:nat 
      ensures 0 <= 1 <= n ==> w(n) <= 3.0*exp(n as R0, k)
    {
      if 0 <= 1 <= n {
        reveal Nat.exp();
        assert exp(n as R0, 2.0) == (n*n) as R0 by { lem_expTwo(n as R0); } 
        assert w(n) <= 3.0*exp(n as R0, k);  
      }
    }
    assert bigOfrom(3.0, 1, w, n => exp(n as R0, k));
  } 
  thm_masterMethodLR2(a, b, c, T6', w, k);
  lem_simplifyPowrTwo();
}

lemma lem_simplifyPowrTwo() 
  requires bigO(liftToR0(T6), n => exp(n as R0, 2.0)*exp(2.0, (n/2) as R0))
  ensures  bigO(liftToR0(T6), n => ((n*n) as R0)*exp(2.0, (n/2) as R0))
{  
  var T6':nat->R0 := liftToR0(T6);

  var c:R0, n0:nat :| bigOfrom(c, n0, T6', n => exp(n as R0, 2.0)*exp(2.0, (n/2) as R0));
  assert forall n:nat :: 0 <= n0 <= n ==> T6'(n) <= c*exp(n as R0, 2.0)*exp(2.0, (n/2) as R0);   
  forall n:nat 
    ensures 0 <= n0+1 <= n ==> T6'(n) <= c*((n*n) as R0)*exp(2.0, (n/2) as R0)
  {
    if 0 <= n0+1 <= n {
      assert T6'(n) <= c*exp(n as R0, 2.0)*exp(2.0, (n/2) as R0);
      lem_expTwo(n as R0);
      assert T6'(n) <= c*((n*n) as R0)*exp(2.0, (n/2) as R0);
    }
  }
  assert forall n:nat :: 0 <= n0+1 <= n ==> T6'(n) <= c*((n*n) as R0)*exp(2.0, (n/2) as R0);  
  assert bigOfrom(c, n0+1, T6', (n:nat) => ((n*n) as R0)*exp(2.0, (n/2) as R0)); 
}

//**************************************************************************//

// Recurrence:
//   T7(n) = / 0                     , n <= 1
//           \ T7(n-1) + log2(n+1)   , n > 1
opaque ghost function T7(n:nat) : nat
  decreases n 
{   
  if n <= 1
  then 0  
  else 1*T7(n-1) + log2(n+1) 
}

lemma lem_T7def(n:nat)
  ensures n <= 1 ==> T7(n) == 0
  ensures n > 1  ==> T7(n) == 1*T7(n-1) + log2(n+1) 
{
  reveal T7(); 
}

// Exact closed form:
//   T7(n) = m*n - 2^{m+1} + 2m + 2   , where m=floor(log2(n+1))
// Asymptotic closed form by MT:
//   T7(n) ∈ O(n^2)     
// Thiger bound:
//   T7(n) ∈ Θ(n*log(n))
lemma test_masterMethodForT7lifted()
  ensures bigO(liftToR0(T7), n => exp(n as R0, 2.0))
{
  var a:nat       := 1;
  var b:nat       := 1;
  var c:R0        := 0.0;
  var k:R0        := 1.0; 
  var T7':nat->R0 := liftToR0(T7);
  var w:nat->R0   := liftToR0(n => log2(n+1));

  forall n:nat 
    ensures T7'(n) == TbodyLR2(a, b, c, T7', w, n)
  {
    reveal TbodyLR2;
    lem_T7def(n);
  } 
  assert bigO(w, n => exp(n as R0, k)) by { 
    // we show that c=1 and n0=1
    forall n:nat 
      ensures 0 <= 1 <= n ==> w(n) <= 1.0*exp(n as R0, k)
    {
      if 0 <= 1 <= n {
        assert exp(n as R0, k) == n as R0 by { lem_expOne(n as R0); } // n >= 1
        assert log2(n+1) <= n by { lem_log2nPlus1LEQn(n); }  // n >= 1
        assert w(n) <= 1.0*(n as R0);
      }
    }
    assert bigOfrom(1.0, 1, w, n => exp(n as R0, k));
  } 
  thm_masterMethodLR2(a, b, c, T7', w, k);
}