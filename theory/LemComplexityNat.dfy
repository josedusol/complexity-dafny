include "./math/ExpNat.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemBoundsNat.dfy"
include "./math/LemFunction.dfy"
include "./math/Log2Nat.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityNat.dfy"
include "./ComplexityR0.dfy"
include "./LemComplexity.dfy"
include "./LemComplexityR0.dfy"

/******************************************************************************
  Lemmas about complexity of non-negative integer functions
******************************************************************************/

module LemComplexityNat { 
  import opened ExpNat
  import opened FloorCeil   
  import opened LemBoundsNat
  import opened LemFunction
  import opened Log2Nat
  import opened TypeR0 
  import opened ComplexityNat
  import CR0 = ComplexityR0
  import opened LemComplexity
  import LCR0 = LemComplexityR0

  /******************************************************************************
    Big O basic properties
  ******************************************************************************/
  // Each result is proved in the lifted domain nat->R0
  // and then casted back to nat->nat 

  // Reflexivity
  // f ∈ O(f)
  lemma lem_bigO_refl(f:nat->nat)  
    ensures f in O(f) 
  {  
    var f':nat->R0 := liftToR0(f);
    assert CR0.bigO(f', f')
      by { LCR0.lem_bigO_refl(f'); }
    lem_bigOR0toBigO(f, f);
  }

  // Transitivity
  // If f ∈ O(g) and g ∈ O(h) then f ∈ O(h)
  lemma lem_bigO_trans(f:nat->nat, g:nat->nat, h:nat->nat)  
    requires f in O(g) 
    requires g in O(h) 
    ensures  f in O(h) 
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

  // If f ∈ O(g) and a>0 then a*f ∈ O(g)
  lemma lem_bigO_constFactor(f:nat->nat, g:nat->nat, a:nat)  
    requires f in O(g) 
    requires a > 0
    ensures  (n => a*f(n)) in O(g) 
  {  
    var f':nat->R0 := liftToR0(f);
    var g':nat->R0 := liftToR0(g); 
    var a':R0 := a as R0; 
    assert CR0.bigO(f', g') 
      by { lem_bigOtoBigOR0(f, g); } 
    assert CR0.bigO(n => a'*f'(n), g')  
      by { LCR0.lem_bigO_constFactor(f', g', a'); }
    lem_bigOR0toBigO(n => a*f(n), g)
      by { lem_funExt(liftToR0(n => a*f(n)), n => a'*f'(n)) 
             by { assert forall n:nat :: liftToR0(n => a*f(n))(n) == (n => a'*f'(n))(n); } 
         }
  } 

  // If f1 ∈ O(g1) and f2 ∈ O(g2) then f1+f2 ∈ O(g1+g2)
  lemma lem_bigO_sum(f1:nat->nat, g1:nat->nat, f2:nat->nat, g2:nat->nat)  
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  (n => f1(n)+f2(n)) in O(n => g1(n)+g2(n)) 
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
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  (n => f1(n)*f2(n)) in O(n => g1(n)*g2(n))  
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
    lem_funExt(liftToR0(n => f1(n)*f2(n)), n => f1'(n)*f2'(n)) 
      by { lem_etaApp(n => f1'(n)*f2'(n)); } 
    lem_funExt(liftToR0(n => g1(n)*g2(n)), n => g1'(n)*g2'(n)) 
      by { lem_etaApp(n => g1'(n)*g2'(n)); }
    lem_bigOR0toBigO(n => f1(n)*f2(n), n => g1(n)*g2(n));
  }   

  // If f ∈ O(g) then f+g ∈ Θ(g)
  lemma lem_bigO_sumSimp(f:nat->nat, g:nat->nat)  
    requires f in O(g) 
    ensures  (n => f(n)+g(n)) in Th(g) 
  {
    var f':nat->R0 := liftToR0(f);
    var g':nat->R0 := liftToR0(g);
    assert CR0.bigO(f', g') 
      by { lem_bigOtoBigOR0(f, g); } 
    assert CR0.bigTh(n => f'(n)+g'(n), g')  
      by { LCR0.lem_bigO_sumSimp(f', g'); }   
    lem_funExt(liftToR0(n => f(n)+g(n)), n => f'(n)+g'(n));  
    lem_funExt(liftToR0(g), g');  
    lem_bigThR0toBigTh(n => f(n)+g(n), g);           
  }

  // If f ∈ O(g+h) and g ∈ O(h) then f ∈ O(h)
  lemma lem_bigO_sumSimp2(f:nat->nat, g:nat->nat, h:nat->nat)  
    requires f in O(n => g(n)+h(n)) 
    requires g in O(h) 
    ensures  f in O(h)
  {
    lem_bigO_sumSimp(g, h);
    lem_bigTh_defEQdef2(n => g(n)+h(n), h);
    assert bigO(n => g(n)+h(n), h);
    lem_bigO_trans(f, n => g(n)+h(n), h);
  }

  // Any constant function have constant growth
  lemma lem_bigO_constGrowth(f:nat->nat, a:nat)  
    requires forall n:nat :: f(n) == a
    ensures  f in O(constGrowth())
  {  
    var fr:nat->R0 := liftToR0(f);
    var cr:nat->R0 := liftToR0(constGrowth());
    assert CR0.bigO(fr, CR0.constGrowth()) 
      by { LCR0.lem_bigO_constGrowth(fr, a as R0); }  
    lem_funExt(liftToR0(constGrowth()), CR0.constGrowth());
    lem_bigOR0toBigO(f, constGrowth());  
  }

  /******************************************************************************
    Big O basic properties lifted to sets
  ******************************************************************************/
  // Each result follows from it's corresponding non-set lifted property

  // This is lem_bigO_sum lifted to sets
  // If f1 ∈ O(g1) and f2 ∈ O(g2) then O(f1+f2) ⊆ O(g1+g2)
  lemma lem_bigOset_sum(f1:nat->nat, g1:nat->nat, f2:nat->nat, g2:nat->nat)  
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  O(n => f1(n)+f2(n)) <= O(n => g1(n)+g2(n)) 
  {  
    forall h:nat->nat | h in O(n => f1(n)+f2(n)) 
      ensures h in O(n => g1(n)+g2(n)) 
    {
      assert h in O(n => f1(n)+f2(n));  
      assert (n => f1(n)+f2(n)) in O(n => g1(n)+g2(n)) 
        by { lem_bigO_sum(f1, g1, f2, g2);  }
      lem_bigO_trans(h, n => f1(n)+f2(n), n => g1(n)+g2(n));  
    }
  }  

  // This is lem_bigO_prod lifted to sets
  // If f1 ∈ O(g1) and f2 ∈ O(g2) then O(f1*f2) ⊆ O(g1*g2)
  lemma lem_bigOset_prod(f1:nat->nat, g1:nat->nat, f2:nat->nat, g2:nat->nat)  
    requires f1 in O(g1) 
    requires f2 in O(g2)
    ensures  O(n => f1(n)*f2(n)) <= O(n => g1(n)*g2(n)) 
  {  
    forall h:nat->nat | h in O(n => f1(n)*f2(n)) 
      ensures h in O(n => g1(n)*g2(n)) 
    {
      assert h in O(n => f1(n)*f2(n));  
      assert (n => f1(n)*f2(n)) in O(n => g1(n)*g2(n)) 
        by { lem_bigO_prod(f1, g1, f2, g2);  }
      lem_bigO_trans(h, n => f1(n)*f2(n), n => g1(n)*g2(n));  
    }
  }   

  // This is lem_bigO_sumSimp lifted to sets
  // If f ∈ O(g) then O(f+g) = O(g)
  lemma lem_bigOset_sumSimp(f:nat->nat, g:nat->nat)  
    requires f in O(g) 
    ensures  O(n => f(n)+g(n)) == O(g)
  {
    // prove O(f+g) ⊆ O(g)
    forall h:nat->nat | h in O(n => f(n)+g(n)) 
      ensures h in O(g) 
    {
      assert h in O(n => f(n)+g(n));  
      assert (n => f(n)+g(n)) in O(g) 
        by { lem_bigO_sumSimp(f, g);
             lem_bigTh_defEQdef2(n => f(n)+g(n), g); }
      lem_bigO_trans(h, n => f(n)+g(n), g);  
    }    

    // prove O(g) ⊆ O(f+g)
    forall h:nat->nat | h in O(g)
      ensures h in O(n => f(n)+g(n)) 
    {
      assert h in O(g);  

      assert g in Th(n => f(n)+g(n)) 
        by { lem_bigO_sumSimp(f, g); 
             lem_bigTh_defEQdef2(n => f(n)+g(n), g);
             lem_bigTh_sim(n => f(n)+g(n), g); }
      
      assert g in O(n => f(n)+g(n)) 
        by { lem_bigTh_defEQdef2(g, n => f(n)+g(n)); }

      lem_bigO_trans(h, g, n => f(n)+g(n));  
    }     
  }

  /******************************************************************************
    Big Ω basic properties
  ******************************************************************************/

  // Reflexivity
  // f ∈ Ω(f)
  lemma lem_bigOm_refl(f:nat->nat)  
    ensures f in Om(f) 
  {  
    // we show that c=1 and n0=0
    var c:nat, n0:nat := 1, 0;
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) >= c*f(n);
    assert bigOmFrom(c, n0, f, f);
  } 

  /******************************************************************************
    Big Θ basic properties
  ******************************************************************************/

  // Reflexivity
  // f ∈ O(f)
  lemma lem_bigTh_refl(f:nat->nat)  
    ensures f in Th(f) 
  {  
    lem_bigO_refl(f); 
    lem_bigOm_refl(f);
    lem_bigTh_defEQdef2(f, f);
  }  

  // Simmetry
  // If f ∈ Θ(g) then g ∈ Θ(f)
  lemma {:axiom} lem_bigTh_sim(f:nat->nat, g:nat->nat)  
    requires f in Th(g) 
    ensures  g in Th(f)

  // Zero function has zero growth
  lemma lem_bigTh_zeroGrowth(f:nat->nat)  
    requires forall n:nat :: f(n) == 0
    ensures  f in Th(zeroGrowth())
  {  
    var fr:nat->R0 := liftToR0(f);
    var cr:nat->R0 := liftToR0(zeroGrowth());
    assert CR0.bigTh(fr, CR0.zeroGrowth()) 
      by { LCR0.lem_bigTh_zeroGrowth(fr); }  
    lem_funExt(liftToR0(zeroGrowth()), CR0.zeroGrowth());
    lem_bigThR0toBigTh(f, zeroGrowth());  
  }    

  /******************************************************************************
    bigTh and bigTh2 are equivalent definitions of Big Θ
  ******************************************************************************/
 
  lemma lem_bigTh_defEQdef2(f:nat->nat, g:nat->nat)  
    ensures bigTh(f, g) <==> bigTh2(f, g)
  {
    var f':nat->R0 := liftToR0(f);
    var g':nat->R0 := liftToR0(g);
    
    assert bigTh(f, g) ==> bigTh2(f, g) by {
      if bigTh(f, g) {
        assert CR0.bigTh(f', g')
          by { lem_bigThtoBigThR0(f, g); }
        assert CR0.bigTh(f', g') ==> CR0.bigTh2(f', g')
          by { LCR0.lem_bigTh_defIMPdef2(f', g'); }
        assert CR0.bigTh2(f', g');
        assert bigTh2(f, g)
          by { lem_bigTh2R0toBigTh2(f, g); }  
      }
    }

    assert bigTh2(f, g) ==> bigTh(f, g) by {
      if bigTh2(f, g) {
        assert CR0.bigTh2(f', g')
          by { lem_bigTh2toBigTh2R0(f, g); }
        assert CR0.bigTh2(f', g') ==> CR0.bigTh(f', g')
          by { LCR0.lem_bigTh_def2IMPdef(f', g'); }
        assert CR0.bigTh(f', g');
        assert bigTh(f, g)
          by { lem_bigThR0toBigTh(f, g); }  
      }
    }
  }

  // A stronger way to conclude a program counter t is Θ(g) for input size n
  lemma lem_bigTh_tIsBigTh2(n:nat, t:nat, g:nat->nat)  
    requires exists f:nat->nat :: f(n) == t && bigTh(f, g)
    ensures  tIsBigTh(n, t, g) 
  {
    var f:nat->nat :| f(n) == t && bigTh(f, g);
    lem_bigTh_defEQdef2(f, g);
  }

  /******************************************************************************
    Common growth rates comparison
  ******************************************************************************/

  // 0 ∈ O(f(n)) 
  lemma lem_bigO_zeroBigOany(f:nat->nat)
    ensures zeroGrowth() in O(f) 
  {
    var c:nat, n0:nat := 1, 0;
    forall n:nat | 0 <= n0 <= n 
      ensures zeroGrowth()(n) <= c*f(n)
    {
      calc {
           zeroGrowth()(n);
        == 0;
        <= 1*f(n);             
      }
    }
    assert bigOfrom(c, n0, zeroGrowth(), f);
  }   

  // 1 ∈ O(log2(n)) 
  lemma lem_bigO_constBigOlog2()
    ensures constGrowth() in O(log2Growth()) 
  {
    var c:nat, n0:nat := 1, 2;
    forall n:nat | 0 <= n0 <= n 
      ensures constGrowth()(n) <= c*log2Growth()(n)
    {
      calc {
           constGrowth()(n); 
        == 1;
        <= { lem_logGEQone(n); }
           1*log2Growth()(n);      
        == c*log2Growth()(n);          
      }
    }
    assert bigOfrom(c, n0, constGrowth(), log2Growth());      
  } 

  // k >= 1 ==> 1 ∈ O(n^k)  
  lemma lem_bigO_constBigOpoly(k:nat)
    requires k >= 1
    ensures  constGrowth() in O(polyGrowth(k)) 
  {
    // Follows from transitivity of 1 ∈ O(log2(n)) and log2(n) ∈ O(n^k)  
    assert constGrowth() in O(log2Growth())  by { lem_bigO_constBigOlog2(); }
    assert log2Growth()  in O(polyGrowth(k)) by { lem_bigO_log2BigOpoly(k); }
    lem_bigO_trans(constGrowth(), log2Growth(), polyGrowth(k));
  }   

  // 1 ∈ O(n)  
  lemma lem_bigO_constBigOlin()
    ensures constGrowth() in O(linGrowth())  
  {
    // Follows from transitivity of 1 ∈ O(log2(n)) and log2(n) ∈ O(n)  
    assert constGrowth() in O(log2Growth()) by { lem_bigO_constBigOlog2(); }
    assert log2Growth()  in O(linGrowth())  by { lem_bigO_log2BigOlin(); }
    lem_bigO_trans(constGrowth(), log2Growth(), linGrowth());
  }    

  // b >= 2 ==> 1 ∈ O(b^n)  
  lemma lem_bigO_constBigOexp(b:nat)
    requires b >= 2
    ensures  constGrowth() in O(expGrowth(b)) 
  {
    // Follows from transitivity of 1 ∈ O(n) and n ∈ O(b^n)  
    assert constGrowth() in O(linGrowth())  by { lem_bigO_constBigOlin(); }
    assert linGrowth()   in O(expGrowth(b)) by { lem_bigO_linBigOexp(b); }
    lem_bigO_trans(constGrowth(), linGrowth(), expGrowth(b));
  }      

  // log2(n) ∈ O(n) 
  lemma lem_bigO_log2BigOlin()
    ensures log2Growth() in O(linGrowth())
  { 
    var c:nat, n0:nat := 1, 1;
    forall n:nat | 0 <= n0 <= n
      ensures log2Growth()(n) <= c*linGrowth()(n)
    {
      calc {      
           log2Growth()(n); 
        == log2(n);
        <= { lem_log2nLEQnMinus1(n); }
           n-1;
        <= c*n;
        == { lem_expn1(n); }
           c*exp(n, 1);
        == c*linGrowth()(n);
      }
    }
    assert bigOfrom(c, n0, log2Growth(), linGrowth());
  }

  // log2(n+1) ∈ O(n) 
  lemma lem_bigO_log2BigOlinV2()
    ensures log2Plus1Growth() in O(linGrowth())
  { 
    // we show that c=1 and n0=1
    var c:nat, n0:nat := 1, 1;
    forall n:nat | 0 <= n0 <= n
      ensures log2Plus1Growth()(n) <= c*linGrowth()(n)
    {
      calc {      
           log2Plus1Growth()(n); 
        == log2(n+1);
        <= { lem_log2nPlus1LEQn(n); }
           n;
        <= c*n;
        == { lem_expn1(n); }
           c*exp(n, 1);
        == c*linGrowth()(n);
      }
    }
    assert bigOfrom(c, n0, log2Plus1Growth(), linGrowth());
  }

  // k >= 1 ==> log2(n) ∈ O(n^k) 
  lemma lem_bigO_log2BigOpoly(k:nat)
    requires k >= 1
    ensures  log2Growth() in O(polyGrowth(k))
  { 
    // Follows from transitivity of log2(n) ∈ O(n) and n ∈ O(n^k)  
    assert log2Growth() in O(linGrowth())   by { lem_bigO_log2BigOlin(); }
    assert linGrowth()  in O(polyGrowth(k)) by { lem_bigO_linBigOpoly(k); }
    lem_bigO_trans(log2Growth(), linGrowth(), polyGrowth(k));   
  }

  // k >= 1 ==> n ∈ O(n^k) 
  lemma lem_bigO_linBigOpoly(k:nat)
    requires k >= 1
    ensures  linGrowth() in O(polyGrowth(k)) 
  { 
    // we show that c=1 and n0=1
    var c:nat, n0:nat := 1, 1;
    forall n:nat | 0 <= n0 <= n
      ensures linGrowth()(n) <= c*polyGrowth(k)(n)
    {
      calc {      
           linGrowth()(n); 
        == exp(n, 1);        
        <= { lem_expMonoIncr(n, 1, k); }
           exp(n, k);
        <= c*exp(n, k);
        == c*polyGrowth(k)(n);
      }
    }
    assert bigOfrom(c, n0, linGrowth(), polyGrowth(k));
  }

  // n ∈ O(n^2) 
  lemma lem_bigO_linBigOquad()
    ensures linGrowth() in O(quadGrowth()) 
  { 
    lem_bigO_linBigOpoly(2);
  }

  // n ∈ O(n^3) 
  lemma lem_bigO_linBigOcubic()
    ensures linGrowth() in O(cubicGrowth()) 
  { 
    lem_bigO_linBigOpoly(3);
  }  

  // n^2 ∈ O(2^n)  
  lemma lem_bigO_quadBigOexp()
    ensures quadGrowth() in O(exp2Growth())
  { 
    // we show that c=1 and n0=4
    var c:nat, n0:nat := 1, 4;
    forall n:nat | 0 <= n0 <= n
      ensures quadGrowth()(n) <= c*exp2Growth()(n)
    {
      calc {      
           quadGrowth()(n); 
        == exp(n, 2);        
        <= { lem_expn2LEQexp2n(n); }   
           exp(2, n);
        <= c*exp(2, n);
        == c*exp2(n);
        == c*exp2Growth()(n);
      }
    }
    assert bigOfrom(c, n0, quadGrowth(), exp2Growth());
  }

  // n ∈ O(2^n)   
  lemma lem_bigO_linBigOexp2()
    ensures linGrowth() in O(exp2Growth()) 
  { 
    // Follows from transitivity of n ∈ O(n^2) and n^2 ∈ O(2^n)  
    assert linGrowth()  in O(quadGrowth()) by { lem_bigO_linBigOquad(); }
    assert quadGrowth() in O(exp2Growth()) by { lem_bigO_quadBigOexp(); }
    lem_bigO_trans(linGrowth(), quadGrowth(), exp2Growth());
  }

  // n ∈ O(b^n)  
  lemma lem_bigO_linBigOexp(b:nat)
    requires b >= 2
    ensures  linGrowth() in O(expGrowth(b)) 
  { 
    // Follows from transitivity of n ∈ O(2^n) and 2^n ∈ O(b^n)  
    assert linGrowth()  in O(exp2Growth()) by { lem_bigO_linBigOexp2(); }
    assert exp2Growth() in O(expGrowth(b)) by { lem_bigO_exp2BigOexp(b); }
    lem_bigO_trans(linGrowth(), exp2Growth(), expGrowth(b));
  }  

  // b >= 2 ==> 2^n ∈ O(b^n)  
  lemma lem_bigO_exp2BigOexp(b:nat)
    requires b >= 2
    ensures  exp2Growth() in O(expGrowth(b))
  {
    // we show that c=1 and n0=1
    var c:nat, n0:nat := 1, 1;
    forall n:nat | 0 <= n0 <= n
      ensures exp2Growth()(n) <= c*expGrowth(b)(n)
    {
      calc {      
           exp2Growth()(n); 
        == exp2(n);        
        == exp(2, n);
        <= { lem_expBaseMonoIncr(n, 2, b); }
           exp(b, n);
        <= c*exp(b, n);
        == c*expGrowth(b)(n);
      }
    }
    assert bigOfrom(c, n0, exp2Growth(), expGrowth(b));    
  }

}