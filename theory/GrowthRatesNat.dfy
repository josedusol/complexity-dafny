include "./math/ExpNat.dfy"
include "./math/Factorial.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemBoundsNat.dfy"
include "./math/LemFunction.dfy"
include "./math/LogNat.dfy"
include "./math/Misc.dfy"
include "./math/SqrtNat.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityNat.dfy"

/**************************************************************************
  Common growth rates
**************************************************************************/

module GrowthRatesNat { 
  import opened ExpNat
  import opened Factorial  
  import opened FloorCeil   
  import opened Misc 
  import opened LemBoundsNat
  import opened LemFunction
  import opened LogNat
  import opened SqrtNat
  import opened TypeR0 

  import opened ComplexityNat

  ghost function constGrowth() : nat->nat
  {   
    n => 1
  }

  ghost function logGrowth() : nat->nat
  {   
    n => if n>0 then log2(n) else 0
  }

  ghost function logGrowth2() : nat->nat
  {   
    n => log2(n+1)
  }

  ghost function sqrtGrowth() : nat->nat
  {   
    n => sqrt(n)
  }

  ghost function linGrowth() : nat->nat
  {   
    n => pow(n,1)
  }

  ghost function quadGrowth() : nat->nat
  {   
    n => pow(n,2)
  }

  ghost function cubicGrowth() : nat->nat
  {   
    n => pow(n,3)
  }

  ghost function polyGrowth(k:nat) : nat->nat
  {   
    n => pow(n,k)
  }

  // ghost function polyGrowthR0(k:R0) : nat->R0
  // {   
  //   n => powr(n as R0,k)
  // }

  ghost function expGrowth() : nat->nat
  {   
    n => pow(2,n)
  }

  ghost function facGrowth() : nat->nat
  {   
    n => fac(n)
  }

  ghost function dexpGrowth() : nat->nat
  {   
    n => pow(2,pow(2,n))
  }

  // log2(n) ∈ O(n) 
  lemma lem_bigO_logBigOlin()
    ensures bigO(logGrowth(), linGrowth()) 
  { 
    // we show that c=1 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures logGrowth()(n) <= 1*linGrowth()(n)
    {
      if 0 <= 1 <= n {
        reveal pow();
        lem_log2nLEQnMinus1(n);
        assert logGrowth()(n) <= 1*linGrowth()(n);
      }
    }
    assert bigOfrom(1, 1, logGrowth(), linGrowth());
  }

  // log2(n+1) ∈ O(n) 
  lemma lem_bigO_logBigOlinV2()
    ensures bigO(logGrowth2(), linGrowth()) 
  { 
    // we show that c=1 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures logGrowth2()(n) <= 1*linGrowth()(n)
    {
      if 0 <= 1 <= n {
        reveal pow();
        lem_log2nPlus1LEQn(n);
        assert logGrowth2()(n) <= 1*linGrowth()(n);
      }
    }
    assert bigOfrom(1, 1, logGrowth2(), linGrowth());
  }

  // n ∈ O(n^2) 
  lemma lem_bigO_linBigOquad()
    ensures bigO(linGrowth(), quadGrowth()) 
  { 
    // we show that c=1 and n0=0
    forall n:nat | 0 <= 0 <= n
      ensures linGrowth()(n) <= 1*quadGrowth()(n)
    {
      if 0 <= 0 <= n {
        reveal pow();
        lem_nLQpown2(n);
        assert linGrowth()(n) <= 1*quadGrowth()(n);
      }
    }
    assert bigOfrom(1, 0, linGrowth(), quadGrowth());
  }

  // n^2 ∈ O(2^n)  
  lemma lem_bigO_quadBigOexp()
    ensures bigO(quadGrowth(), expGrowth()) 
  { 
    // we show that c=1 and n0=4
    forall n:nat | 0 <= 4 <= n
      ensures quadGrowth()(n) <= 1*expGrowth()(n)
    {
      if 0 <= 4 <= n {
        reveal pow();
        lem_pown2LQpow2n(n);
        assert quadGrowth()(n) <= 1*expGrowth()(n);
      }
    }
    assert bigOfrom(1, 4, quadGrowth(), expGrowth());
  }

  // n ∈ O(2^n)  
  // Follows from transitivity of n ∈ O(n^2) and n^2 ∈ O(2^n)  
  lemma lem_bigO_linBigOexp()
    ensures bigO(linGrowth(), expGrowth()) 
  { 
    assert bigO(linGrowth(), quadGrowth()) by { lem_bigO_linBigOquad(); }
    assert bigO(quadGrowth(), expGrowth()) by { lem_bigO_quadBigOexp(); }
    lem_bigO_trans(linGrowth(), quadGrowth(), expGrowth());
  }

}