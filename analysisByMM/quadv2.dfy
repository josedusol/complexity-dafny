include "../theory/math/ExpReal.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"
include "../theory/MasterLR.dfy"

import opened ExpReal
import opened LemFunction
import opened TypeR0
import opened ComplexityR0
import opened MasterLR

method quad(N:nat)
  returns (ghost t:nat, ghost t':nat)
  ensures t == T1(N, N)  
  //ensures bigO(liftToR0((n:nat) => T1(N,n)), polyGrowth(1.0))
  ensures bigO(liftToR0((n:nat) => T1(N,n)), polyGrowth(2.0))
  //ensures bigO(liftToR0((n:nat) => if n<=N then T1(N,N,n) else 0), polyGrowth(2.0))
  //ensures bigO(liftToR0((n:nat) requires n<=N => T1(N,N,n)), polyGrowth(2.0))
{
  var i, j; reveal T1(),T2(); //var M := N;
  i, j, t, t' := 0, 0, 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T1(N, N) - T1(N, N-i) // = T1'(i, N) 
    decreases N - i 
  {
    j := 0; t' := 0; 
    while j != N
      invariant 0 <= j <= N
      invariant t' == T2(N-i, N) - T2(N-i, N-j) // = T2'(j)
      decreases N - j
    {
      // Op. interesante
      j := j+1;
      t' := t'+1;
    }
    i := i+1;
    t := t+t';
  }
  assert t == T1(N, N); 
  lem_T1BigOquad(N);
} 

opaque ghost function T1(N:nat, i:nat): nat
  //requires i <= N
  decreases i
{
  if i <= 0
  then 0
  else T1(N, i-1) + T2(i, N)
}
//opaque ghost function T1(N:nat, M:nat, i:nat): nat
//   decreases i
// {
//   if i <= 0
//   then 0
//   else T1(N, M, i-1) + T2(i, M, M) 
// }

opaque ghost function T2(M:nat, j:nat): nat
  decreases j
{
  if j <= 0
  then 0
  else T2(M, j-1) + 1 
}

lemma lem_T1def(N:nat, i:nat)
  //requires i <= N
  ensures i <= 0 ==> T1(N,i) == 0
  ensures i >  0 ==> T1(N,i) == 1*T1(N,i-1) + T2(i, N)
{
  reveal T1();
}
// lemma lem_T1def(N:nat, M:nat, i:nat)
//   ensures i <= 0 ==> T1(N,M,i) == 0
//   ensures i >  0 ==> T1(N,M,i) == 1*T1(N,M,i-1) + T2(i,M,M)
// {
//   reveal T1();
// }

lemma lem_T2def(M:nat, j:nat)
  //requires j <= M
  ensures j <= 0 ==> T2(M,j) == 0
  ensures j >  0 ==> T2(M,j) == 1*T2(M,j-1) + 1
{
  reveal T2();
}

// lemma {:isolate_assertions} lem_T1BigOquad(N:nat, M:nat)
//   requires N == M
//   ensures bigO(liftToR0((n:nat) => if n<=N then T1(N,N,n) else 0), n => pow(n as R0, 2.0))
// {
//   var a:nat       := 1;
//   var b:nat       := 0;
//   var c:R0        := 0.0;
//   var s:nat       := 1;
//   var k:R0        := 1.0;
//   var T1':nat->R0 := liftToR0((n:nat) => if n<=N then T1(N,N,n) else 0);
//   var w:nat->R0   := liftToR0((n:nat) => if n<=N then T2(N,N,N) else 0);

//   assert b >= s-1; 
//   forall n:nat  
//     ensures T1'(n) == (if n<=N then TbodyLR(a, b, c, s, T1', w, k, n) else 0.0)
//   {  
//     reveal TbodyLR;  
//     //lem_T1def(N, N, n);
//     if n <= N {
//       lem_T1def(N, N, n);
//       // if n <= 0 {
//       //   assert T1'(n) == 0.0;
//       // } else {
//       //   assert T1'(n) == 1.0*T1'(n-1) + (T2(n,N,N) as R0);
//       // } 
//     }
//   } 
//   //lem_T2BigOlin(N, N);
//   //assert bigOR0(liftToR0(n => T2(N,N,n)), n => powr0(n as R0, 1.0));

//   assert bigOR0(w, n => powr0(n as R0, k)) by {
//     lem_T2BigOlin(N, N);
//     var c:R0, n0:nat :| bigOR0from(c, n0, liftToR0(n => T2(N,N,n)), n => powr0(n as R0, 1.0));
//     assert forall n:nat :: 0 <= n0 <= n ==> liftToR0(n => T2(N,N,n))(n) <= c*powr0(n as R0, 1.0);
 
//     forall n:nat | 0 <= n0 <= n
//       ensures w(n) <= c*powr0(n as R0, k)
//     {
//        if n <= N {
//          assert T2(N,N,n) <= T2(N,N,N);
//          assert liftToR0(n => T2(N,N,n))(n) <= c*powr0(n as R0, 1.0);
//          assert liftToR0(n => T2(N,N,N))(n) <= c*powr0(n as R0, 1.0);
//          assert liftToR0((n:nat) => if n<=N then T2(n,N,N) else 0)(n) <= c*powr0(n as R0, k);
//        }
//     }
//   }
//     //by { lem_T2BigOlin(N, M); }
//    //by { lem_T1BigOquadAux(M); }
//   thm_masterMethodLR(a, b, c, s, T1', w, k); 
// }

// lemma {:isolate_assertions} lem_T1BigOquad(N:nat)
//   ensures bigOR0(liftToR0((n:nat) => T1(N,n)), n => powr0(n as R0, 2.0))
// {
//   var a:nat       := 1;
//   var b:nat       := 0;
//   var c:R0        := 0.0;
//   var s:nat       := 1;
//   var k:R0        := 1.0;
//   var T1':nat->R0 := liftToR0((n:nat) => T1(N,n));
//   var w:nat->R0   := liftToR0((n:nat) => T2(N,N));

//   assert b >= s-1; 
//   forall n:nat  
//     ensures T1'(n) == TbodyLR(a, b, c, s, T1', w, k, n)
//   {  
//     reveal TbodyLR;  
//     lem_T1def(N, n);
//   } 
//   //lem_T2BigOlin(N, N);
//   //assert bigOR0(liftToR0(n => T2(N,N,n)), n => powr0(n as R0, 1.0));

//   assert bigOR0(w, n => powr0(n as R0, k)) by {
//     lem_T2BigOlin(N);
//     var c:R0, n0:nat :| bigOR0from(c, n0, liftToR0(n => T2(N,n)), n => powr0(n as R0, 1.0));
//     assert forall n:nat :: 0 <= n0 <= n ==> liftToR0(n => T2(N,n))(n) <= c*powr0(n as R0, 1.0);
 
//     forall n:nat | 0 <= n0+N <= n
//       ensures w(n) <= c*powr0(n as R0, k)
//     {
//        //assume n <= N;
//        assert T2(N,N) <= T2(N,n);
//        assert liftToR0(n => T2(N,n))(n) <= c*powr0(n as R0, 1.0);
//        assert liftToR0(n => T2(N,n))(N) == T2(N,N) as R0;
//        assert T2(N,n) as R0 <= c*powr0(n as R0, 1.0);
//        assert T2(N,N) as R0 <= c*powr0(n as R0, 1.0);

//        //assert (T2(N,N) as R0) <= c*powr0(n as R0, k); 
//     }
//   }
//     //by { lem_T2BigOlin(N, M); }
//    //by { lem_T1BigOquadAux(M); }
//   thm_masterMethodLR(a, b, c, s, T1', w, k); 
// }

lemma {:isolate_assertions} lem_T1BigOquad(N:nat)
  ensures bigO(liftToR0((n:nat) => T1(N,n)), n => pow(n as R0, 2.0))
{
  var a:nat       := 1;
  var b:nat       := 0;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 1.0;
  var T1':nat->R0 := liftToR0((n:nat) => T1(N,n));
  var w:nat->R0   := liftToR0((n:nat) => T2(n,N));

  assert b >= s-1; 
  forall n:nat  
    ensures T1'(n) == TbodyLR(a, b, c, s, T1', w, n)
  {  
    reveal TbodyLR;  
    lem_T1def(N, n);
  } 

  assert bigO(w, n => pow(n as R0, k)) by {
    lem_T2BigOlin(N);
    assert bigO(liftToR0(n => T2(N,n)), n => pow(n as R0, 1.0));
    var c2:R0, n0:nat :| bigOfrom(c2, n0, liftToR0(n => T2(N,n)), n => pow(n as R0, 1.0));
    assert forall n:nat :: 0 <= n0 <= n ==> liftToR0(n => T2(N,n))(n) <= c2*pow(n as R0, 1.0);
    
  }
    //by { lem_T2BigOlin(N, M); }
  //by { lem_T1BigOquadAux(M); }
  thm_masterMethodLR(a, b, c, s, T1', w, k); 
  //assert bigOR0(liftToR0((n:nat) => if n <= N then T1(N, n) else 0), n => powr0(n as R0, 2.0));
}

// lemma {:isolate_assertions} lem_T1BigOquadAux(N:nat)
//   ensures bigOR0(liftToR0(n => T2(N)), n => powr0(n as R0, 1.0))
// {
//   var k:R0 := 1.0;
//   var w:nat->R0 := liftToR0(n => T2(N)); 

//   var c:R0 := T2(N) as R0;
//   var n0:nat := 1; 
//   forall n:nat | 0 <= 1 <= n
//     ensures w(n) <= c * powr0(n as R0, k) as R0
//   {
//     assert T2(N) as R0 <= c * n as R0
//       by { assert T2(N) <= (T2(N))*n; }
//     assert powr0(n as R0, k) == n as R0 
//       by { assert n as R0 > 0.0; lem_powrOne(n as R0); }
//     assert T2(N) as R0 <= c * powr0(n as R0, k); 
//     assert w(n) <= c * powr0(n as R0, k)
//       by { assert w(n) == T2(N) as R0; }
//   }
//   assert bigOR0from(c, n0, w, n => powr0(n as R0, k));  
// }



lemma lem_T2BigOlin(N:nat)
  ensures bigO(liftToR0(n => T2(N,n)), n => pow(n as R0, 1.0)) 
{
  var a:nat       := 1;
  var b:nat       := 0;
  var c:R0        := 0.0; 
  var s:nat       := 1;
  var k:R0        := 0.0;
  var T2':nat->R0 := liftToR0(n => T2(N,n));
  var w:nat->R0   := liftToR0(n => 1);

  forall n:nat 
    ensures T2'(n) == TbodyLR(a, b, c, s, T2', w, n)
  {
    reveal TbodyLR;
    //if n <= N {
      lem_T2def(N,n); 
    //}
  } 
  assert bigO(w, n => pow(n as R0, k)) by {   
    // we show that c=1 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures w(n) <= 1.0*polyGrowth(k)(n)
    {
      assert pow(n as R0, k) == 1.0 by { lem_powZeroAll(); }
      assert w(n) <= 1.0*polyGrowth(k)(n); 
    }
    assert bigOfrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR(a, b, c, s, T2', w, k);
}