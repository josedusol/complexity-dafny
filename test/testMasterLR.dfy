include "../theory/math/ExpReal.dfy"
include "../theory/math/LemBoundsNat.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/Log2Nat.dfy"
include "../theory/math/SumInt.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"
include "../theory/MasterLR.dfy"

import opened ExpReal
import opened LemBoundsNat
import opened LemFunction
import opened Log2Nat
import opened TypeR0
import opened ComplexityR0
import opened MasterLR

// Recurrence 1:
//   T1(n) = / 0             , n <= 0
//           \ T1(n-1) + 1   , n > 0
opaque ghost function T1(n:nat) : nat
  decreases n 
{   
  if n <= 0
  then 0  
  else T1(n-1) + 1
} 
 
lemma lem_T1def(n:nat)
  ensures n <= 0 ==> T1(n) == 0
  ensures n > 0  ==> T1(n) == 1*T1(n-1) + 1
{
  reveal T1();
}

// Exact closed form:
//   T1(n) = n
// Asymptotic closed form:
//   T1(n) in O(n)
lemma test_masterMethodForT1lifted()
  ensures liftToR0(T1) in O(n => exp(n as R0, 1.0))
{
  var a:nat       := 1;
  var b:nat       := 0;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 0.0;
  var T1':nat->R0 := liftToR0(T1);
  var w:nat->R0   := liftToR0(n => 1);

  assert b >= s-1;  
  forall n:nat 
    ensures T1'(n) == TbodyLR(a, b, c, s, T1', w, n)
  {
    reveal TbodyLR;
    lem_T1def(n);
  }           
  assert w in O(n => exp(n as R0, k)) by {   
    // we show that c=1 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures w(n) <= 1.0*polyGrowth(k)(n)
    {
      assert exp(n as R0, k) == 1.0 by { lem_exp_ZeroAuto(); }
      assert w(n) <= 1.0*polyGrowth(k)(n); 
    }
    assert bigOfrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR(a, b, c, s, T1', w, k);
}   

//**************************************************************************//

// Recurrence 2:
//   T2(n) = / 0             , n <= 2
//           \ T2(n-1) + 1   , n > 2
opaque ghost function T2(n:nat) : nat
  decreases n
{
  if n <= 2
  then 0  
  else T2(n-1) + 1 
}

lemma lem_T2def(n:nat)
  ensures n <= 2 ==> T2(n) == 0
  ensures n > 2  ==> T2(n) == 1*T2(n-1) + 1
{
  reveal T2();
}

// Exact closed form:
//   T2(n) = 1/4*(2*n - (-1)^n - (-1)^(2 n) - 2)
// Asymptotic closed form:
//   T2(n) in O(n)
lemma test_masterMethodForT2lifted() 
  ensures liftToR0(T2) in O(n => exp(n as R0, 1.0))
{
  var a:nat       := 1;
  var b:nat       := 2;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 0.0;
  var T2':nat->R0 := liftToR0(T2);
  var w:nat->R0   := liftToR0(n => 1);

  assert b >= s-1;  
  forall n:nat 
    ensures T2'(n) == TbodyLR(a, b, c, s, T2', w, n)
  {
    reveal TbodyLR;
    lem_T2def(n);
  }
  assert w in O(n => exp(n as R0, k)) by {  // k=0
    // we show that c=1 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures w(n) <= 1.0*polyGrowth(k)(n)
    {
      assert polyGrowth(k)(n) == 1.0 by { lem_exp_ZeroAuto(); }
      assert 1.0 <= 1.0*polyGrowth(k)(n); 
    }
    assert bigOfrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR(a, b, c, s, T2', w, k); 
} 

//**************************************************************************//

// Recurrence 3:
//   T3(n) = / 0             , n <= 4
//           \ T3(n-1) + 1   , n > 4
opaque ghost function T3(n:nat) : nat
  decreases n
{
  if n <= 4
  then 0  
  else T3(n-1) + 1 
}

lemma lem_T3def(n:nat)
  ensures n <= 4 ==> T3(n) == 0
  ensures n > 4  ==> T3(n) == 1*T3(n-1) + 1
{
  reveal T3();
}

// Exact closed form:
//   T2(n) = 1/4*(2*n - (-1)^n - (-1)^(2 n) - 2)
// Asymptotic closed form:
//   T2(n) in O(n)
lemma test_masterMethodForT3lifted() 
  ensures liftToR0(T3) in O(n => exp(n as R0, 1.0))
{
  var a:nat       := 1;
  var b:nat       := 4;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 0.0;
  var T3':nat->R0 := liftToR0(T3);
  var w:nat->R0   := liftToR0(n => 1);

  assert b >= s-1;  
  forall n:nat 
    ensures T3'(n) == TbodyLR(a, b, c, s, T3', w, n)
  {
    reveal TbodyLR;
    lem_T3def(n);
  }
  assert w in O(n => exp(n as R0, k)) by {  // k=0
    // we show that c=1 and n0=1
    forall n:nat | 0 <= 1 <= n 
      ensures w(n) <= 1.0*polyGrowth(k)(n)
    {
      assert polyGrowth(k)(n) == 1.0 by { lem_exp_ZeroAuto(); }
      assert 1.0 <= 1.0*polyGrowth(k)(n); 
    }
    assert bigOfrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR(a, b, c, s, T3', w, k); 
} 