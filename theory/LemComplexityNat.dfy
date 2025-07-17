include "./math/ExpNat.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemBoundsNat.dfy"
include "./math/LemFunction.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityNat.dfy"
include "./ComplexityR0.dfy"
include "./LemComplexity.dfy"
include "./LemComplexityR0.dfy"

/**************************************************************************
  Lemmas about complexity of non-negative integer functions
**************************************************************************/

module LemComplexityNat { 
  import opened ExpNat
  import opened FloorCeil   
  import opened LemBoundsNat
  import opened LemFunction
  import opened TypeR0 
  import opened ComplexityNat
  import CR0 = ComplexityR0
  import opened LemComplexity
  import LCR0 = LemComplexityR0

  /* BigTheta1 and bigTheta2 are equivalent definitions of Big Θ */
 
  lemma lem_bigTheta_def1EQLdef2(f:nat->nat, g:nat->nat)  
    ensures bigTheta1(f, g) <==> bigTheta2(f, g)
  {
    var f':nat->R0 := liftToR0(f);
    var g':nat->R0 := liftToR0(g); 
    
    assert bigTheta1(f, g) ==> bigTheta2(f, g) by {
      assume {:axiom} bigTheta1(f, g);
      assert CR0.bigTheta1(f', g')
        by { lem_bigT1toBigT1R0(f, g); }
      assert CR0.bigTheta1(f', g') ==> CR0.bigTheta2(f', g')
        by { LCR0.lem_bigTheta_def1IMPLdef2(f', g'); }
      assert CR0.bigTheta2(f', g');
      assert bigTheta2(f, g)
        by { lem_bigT2R0toBigT2(f, g); }  
    }

    assert bigTheta2(f, g) ==> bigTheta1(f, g) by {
      assume {:axiom} bigTheta2(f, g);
      assert CR0.bigTheta2(f', g')
        by { lem_bigT2toBigT2R0(f, g); }
      assert CR0.bigTheta2(f', g') ==> CR0.bigTheta1(f', g')
        by { LCR0.lem_bigTheta_def2IMPLdef1(f', g'); }
      assert CR0.bigTheta1(f', g');
      assert bigTheta1(f, g)
        by { lem_bigT1R0toBigT1(f, g); }  
    }
  }

  /* Big O basic properties */
  // Each result is proved in the lifted domain nat->R0
  // and then casted back to nat->nat 

  // Reflexivity
  // f ∈ O(f)
  lemma lem_bigO_refl(f:nat->nat)  
    ensures bigO(f, f) 
  {  
    var f':nat->R0 := liftToR0(f);
    assert CR0.bigO(f', f')
      by { LCR0.lem_bigO_refl(f'); }
    lem_bigOR0toBigO(f, f);
  }

  // If f ∈ O(g) and a>0 then a*f ∈ O(g)
  lemma lem_bigO_constFactor(f:nat->nat, g:nat->nat, a:nat)  
    requires bigO(f, g) 
    requires a > 0
    ensures  bigO(n => a*f(n), g) 
  {  
    var f':nat->R0 := liftToR0(f);
    var g':nat->R0 := liftToR0(g); 
    var a':R0 := a as R0; 
    assert CR0.bigO(f', g') 
      by { lem_bigOtoBigOR0(f, g); }
    assert CR0.bigO(n => a'*f'(n), g')  
      by { LCR0.lem_bigO_constFactor(f', g', a'); }
    lem_bigOR0toBigO(n => a*f(n), g)
      by { lem_funExt(liftToR0(n => a*f(n)), n => a'*f'(n)); }
  } 

  // If f1 ∈ O(g1) and f2 ∈ O(g2) then f1+f2 ∈ O(g1+g2)
  lemma lem_bigO_sum(f1:nat->nat, g1:nat->nat, f2:nat->nat, g2:nat->nat)  
    requires bigO(f1, g1) 
    requires bigO(f2, g2) 
    ensures  bigO(n => f1(n)+f2(n), n => g1(n)+g2(n)) 
  {  
    var f1':nat->R0 := liftToR0(f1);
    var f2':nat->R0 := liftToR0(f2);
    var g1':nat->R0 := liftToR0(g1); 
    var g2':nat->R0 := liftToR0(g2); 
    assert CR0.bigO(f1', g1') 
      by { lem_bigOtoBigOR0(f1, g1); }
    assert CR0.bigO(f2', g2') 
      by { lem_bigOtoBigOR0(f2, g2); } 
    assert CR0.bigO(n => f1'(n)+f2'(n), n => g1'(n)+g2'(n))  
      by { LCR0.lem_bigO_sum(f1', g1', f2', g2'); }
    lem_funExt(liftToR0(n => f1(n)+f2(n)), n => f1'(n)+f2'(n));
    lem_funExt(liftToR0(n => g1(n)+g2(n)), n => g1'(n)+g2'(n));  
    lem_bigOR0toBigO(n => f1(n)+f2(n), n => g1(n)+g2(n));     
  }

  // If f1 ∈ O(g1) and f2 ∈ O(g2) then f1*f2 ∈ O(g1*g2)
  lemma lem_bigO_prod(f1:nat->nat, g1:nat->nat, f2:nat->nat, g2:nat->nat)  
    requires bigO(f1, g1) 
    requires bigO(f2, g2) 
    ensures  bigO(n => f1(n)*f2(n), n => g1(n)*g2(n))  
  {  
    var f1':nat->R0 := liftToR0(f1);
    var f2':nat->R0 := liftToR0(f2);
    var g1':nat->R0 := liftToR0(g1); 
    var g2':nat->R0 := liftToR0(g2);  
    assert A: CR0.bigO(f1', g1') 
      by { lem_bigOtoBigOR0(f1, g1); }
    assert B: CR0.bigO(f2', g2') 
      by { lem_bigOtoBigOR0(f2, g2); } 
    assert CR0.bigO(n => f1'(n)*f2'(n), n => g1'(n)*g2'(n))  
      by { reveal A, B; LCR0.lem_bigO_prod(f1', g1', f2', g2'); }
    lem_funExt(liftToR0(n => f1(n)*f2(n)), n => f1'(n)*f2'(n));
    lem_funExt(liftToR0(n => g1(n)*g2(n)), n => g1'(n)*g2'(n));
    lem_bigOR0toBigO(n => f1(n)*f2(n), n => g1(n)*g2(n));
  }   

  // Transitivity
  // If f ∈ O(g) and g ∈ O(h) then f ∈ O(h)
  lemma lem_bigO_trans(f:nat->nat, g:nat->nat, h:nat->nat)  
    requires bigO(f, g)
    requires bigO(g, h)
    ensures  bigO(f, h) 
  {  
    var f':nat->R0 := liftToR0(f);
    var g':nat->R0 := liftToR0(g);  
    var h':nat->R0 := liftToR0(h);  
    assert CR0.bigO(f', g') 
      by { lem_bigOtoBigOR0(f, g); }
    assert CR0.bigO(g', h') 
      by { lem_bigOtoBigOR0(g, h); }
    assert CR0.bigO(f', h')  
      by { LCR0.lem_bigO_trans(f', g', h'); }
    lem_bigOR0toBigO(f, h);
  }

  /* Common growth rates comparison */
  
  // log2(n) ∈ O(n) 
  lemma lem_bigO_logBigOlin()
    ensures bigO(logGrowth(), linGrowth()) 
  { 
    // we show that c=1 and n0=1
    var c:nat, n0:nat := 1, 1;
    forall n:nat | 0 <= n0 <= n
      ensures logGrowth()(n) <= c*linGrowth()(n)
    {
      reveal exp();
      lem_log2nLEQnMinus1(n);
      assert logGrowth()(n) <= c*linGrowth()(n);
    }
    assert bigOfrom(c, n0, logGrowth(), linGrowth());
  }

  // log2(n+1) ∈ O(n) 
  lemma lem_bigO_logBigOlinV2()
    ensures bigO(logGrowth2(), linGrowth())
  { 
    // we show that c=1 and n0=1
    var c:nat, n0:nat := 1, 1;
    forall n:nat | 0 <= n0 <= n
      ensures logGrowth2()(n) <= c*linGrowth()(n)
    {
      reveal exp();
      lem_log2nPlus1LEQn(n);
      assert logGrowth2()(n) <= c*linGrowth()(n);
    }
    assert bigOfrom(c, n0, logGrowth2(), linGrowth());
  }

  // n ∈ O(n^2) 
  lemma lem_bigO_linBigOquad()
    ensures bigO(linGrowth(), quadGrowth()) 
  { 
    // we show that c=1 and n0=0
    var c:nat, n0:nat := 1, 0;
    forall n:nat | 0 <= n0 <= n
      ensures linGrowth()(n) <= c*quadGrowth()(n)
    {
      reveal exp();
      lem_nLQexpn2(n);
      assert linGrowth()(n) <= c*quadGrowth()(n);
    }
    assert bigOfrom(c, n0, linGrowth(), quadGrowth());
  }

  // n^2 ∈ O(2^n)  
  lemma lem_bigO_quadBigOexp()
    ensures bigO(quadGrowth(), expGrowth()) 
  { 
    // we show that c=1 and n0=4
    var c:nat, n0:nat := 1, 4;
    forall n:nat | 0 <= n0 <= n
      ensures quadGrowth()(n) <= c*expGrowth()(n)
    {
      reveal exp();
      lem_expn2LQexp2n(n);
      assert quadGrowth()(n) <= c*expGrowth()(n);
    }
    assert bigOfrom(c, n0, quadGrowth(), expGrowth());
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