include "./math/ExpNat.dfy"
include "./math/ExpReal.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemBoundsNat.dfy"
include "./math/LemFunction.dfy"
include "./math/Log2Nat.dfy"
include "./math/LogReal.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityR0.dfy"

/******************************************************************************
  Lemmas about complexity of lifted functions
******************************************************************************/

module LemComplexityR0 { 
  import EN = ExpNat
  import opened ExpReal
  import opened FloorCeil   
  import opened LemBoundsNat
  import opened LemFunction
  import LN = Log2Nat
  import opened LogReal
  import opened TypeR0 
  import opened ComplexityR0

  /******************************************************************************
    bigTh and bigTh2 are equivalent definitions of Big Θ 
  ******************************************************************************/
  
  lemma lem_bigTheta_def1EQLdef2(f:nat->R0, g:nat->R0)  
    ensures bigTh(f, g) <==> bigTh2(f, g)
  {
    assert bigTh(f, g) ==> bigTh2(f, g) by {
      assume {:axiom} bigTh(f, g);
      lem_bigTheta_def1IMPLdef2(f, g);
    }
    assert bigTh2(f, g) ==> bigTh(f, g) by {
      assume {:axiom} bigTh2(f, g);
      lem_bigTh_def2IMPLdef1(f, g);
    }
  }

  lemma lem_bigTheta_def1IMPLdef2(f:nat->R0, g:nat->R0)  
    requires bigTh(f, g) 
    ensures  bigTh2(f, g)
  {
    var c1:R0, n0_1:nat :| bigOmFrom(c1, n0_1, f, g) ; 
    assert H1: forall n:nat :: 0 <= n0_1 <= n ==> c1*g(n) <= f(n);

    var c2:R0, n0_2:nat :| bigOfrom(c2, n0_2, f, g) ; 
    assert H2: forall n:nat :: 0 <= n0_2 <= n ==> f(n) <= c2*g(n);

    var n0 := n0_1 + n0_2;
    forall n:nat | 0 <= n0 <= n
      ensures c1*g(n) <= f(n) <= c2*g(n)
    {
      assert c1*g(n) <= f(n) by { reveal H1; }
      assert f(n) <= c2*g(n) by { reveal H2; }
    }
    assert bigThFrom(c1, c2, n0, f, g);
  }

  lemma lem_bigTh_def2IMPLdef1(f:nat->R0, g:nat->R0)  
    requires bigTh2(f, g) 
    ensures  bigTh(f, g)
  {
    var c1:R0, c2:R0, n0:nat :| bigThFrom(c1, c2, n0, f, g); 
    assert H: forall n:nat :: 0 <= n0 <= n ==> c1*g(n) <= f(n) <= c2*g(n);

    assert A: f in O(g) by {
      forall n:nat | 0 <= n0 <= n
        ensures f(n) <= c2*g(n)
      {
        assert f(n) <= c2*g(n) by { reveal H; }
      }
      assert bigOfrom(c2, n0, f, g);
    }
    assert B: f in Om(g) by {
      forall n:nat | 0 <= n0 <= n
        ensures c1*g(n) <= f(n)
      {
        assert c1*g(n) <= f(n) by { reveal H; }
      }
      assert bigOmFrom(c1, n0, f, g);
    }
    
    assert f in O(g) && f in Om(g) by { reveal A, B; }
  }      

  /******************************************************************************
    Big O basic properties
  ******************************************************************************/

  // Reflexivity
  // f ∈ O(f)
  lemma lem_bigO_refl(f:nat->R0)  
    ensures f in O(f) 
  {  
    // we show that c=1 and n0=0
    var c:R0, n0:nat := 1.0, 0;
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*f(n);
    assert bigOfrom(c, n0, f, f);
  }

  // Transitivity
  // If f ∈ O(g) and g ∈ O(h) then f ∈ O(h)
  lemma lem_bigO_trans(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires f in O(g) 
    requires g in O(h)  
    ensures  f in O(h)  
  {  
    var c1:R0, n1:nat :| bigOfrom(c1, n1, f, g);  
    assert forall n:nat :: 0 <= n1 <= n ==> f(n) <= c1*g(n);
    var c2:R0, n2:nat :| bigOfrom(c2, n2, g, h);  
    assert forall n:nat :: 0 <= n2 <= n ==> g(n) <= c2*h(n);   
    
    // we show that c=c1*c2 and n0=n1+n2
    var c:R0, n0:nat := c1*c2, n1+n2;
    forall n:nat | 0 <= n0 <= n
      ensures f(n) <= c*h(n)
    {
      calc {
           f(n); 
        <= c1*g(n);
        <= { assert g(n) <= c2*h(n); } 
           c1*c2*h(n);     
        == c*h(n);         
      }
    }
    assert bigOfrom(c, n0, f, h);
  }  

  // If f ∈ O(g) and a>0 then a*f ∈ O(g)
  lemma lem_bigO_constFactor(f:nat->R0, g:nat->R0, a:R0)  
    requires f in O(g) 
    requires a > 0.0 
    ensures  (n => a*f(n)) in O(g) 
  {  
    var c:R0, n0:nat :| bigOfrom(c, n0, f, g);  
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);
    
    // we show that c'=a*c and n0'=n0
    assert forall n:nat :: 0 <= n0 <= n ==> a*f(n) <= (a*c)*g(n);
    assert bigOfrom(a*c, n0, n => a*f(n), g);
  }

  // If f1 ∈ O(g1) and f2 ∈ O(g2) then f1+f2 ∈ O(g1+g2)
  lemma lem_bigO_sum(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  (n => f1(n)+f2(n)) in O(n => g1(n)+g2(n)) 
  {  
    var c1:R0, n1:nat :| bigOfrom(c1, n1, f1, g1);  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> f1(n) <= c1*g1(n);
    var c2:R0, n2:nat :| bigOfrom(c2, n2, f2, g2);  
    assert H2: forall n:nat :: 0 <= n2 <= n ==> f2(n) <= c2*g2(n);   
    
    // we show that c=c1+c2 and n0=n1+n2 (not tight but works)
    var c:R0, n0:nat := c1+c2, n1+n2;
    forall n:nat | 0 <= n0 <= n
      ensures f1(n) + f2(n) <= c*(g1(n) + g2(n))
    {
      calc {
           f1(n) + f2(n); 
        <= { reveal H1, H2; }
           c1*g1(n) + c2*g2(n); 
        <= { assert c1 <= c1+c2; assert c2 <= c1+c2; }
           (c1+c2)*g1(n) + (c1+c2)*g2(n);
        == (c1+c2)*(g1(n) + g2(n)); 
        == c*(g1(n) + g2(n));         
      }
    }    
    assert bigOfrom(c, n0, n => f1(n)+f2(n), n => g1(n)+g2(n));
  }

  // If f1 ∈ O(g1) and f2 ∈ O(g2) then f1*f2 ∈ O(g1*g2)
  lemma lem_bigO_prod(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  (n => f1(n)*f2(n)) in O(n => g1(n)*g2(n))  
  {  
    var c1:R0, n1:nat :| bigOfrom(c1, n1, f1, g1);  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> f1(n) <= c1*g1(n);
    var c2:R0, n2:nat :| bigOfrom(c2, n2, f2, g2);  
    assert H2: forall n:nat :: 0 <= n2 <= n ==> f2(n) <= c2*g2(n);   
    
    // we show that c=c1*c2 and n0=n1+n2 (not tight but works)
    var c:R0, n0:nat := c1*c2, n1+n2;
    forall n:nat | 0 <= n0 <= n
      ensures f1(n) * f2(n) <= c*(g1(n) * g2(n))
    {
      calc {
           f1(n) * f2(n); 
        <= { reveal H1, H2; }
           c1*g1(n) * c2*g2(n); 
        == (c1*c2)*(g1(n) * g2(n));
        == c*(g1(n) * g2(n));         
      }
    }  
    assert bigOfrom(c, n0, n => f1(n)*f2(n), n => g1(n)*g2(n));
  }

  // If f ∈ O(g) then f+g ∈ Θ(g)
  lemma lem_bigO_sumSimp(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  (n => f(n)+g(n)) in Th(g)    
  {
    var c:R0, n0:nat :| bigOfrom(c, n0, f, g);  
    assert H1: forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);

    // prove f+g ∈ O(g)
    var c1:R0, n1:nat := c+1.0, n0;
    forall n:nat | 0 <= n1 <= n
      ensures f(n) + g(n) <= c1*g(n)
    {
      calc {
           f(n) + g(n); 
        <= { reveal H1; }
           c*g(n) + g(n); 
        == (c + 1.0)*g(n);
        == c1*g(n);         
      }
    }  
    assert bigOfrom(c1, n1, n => f(n)+g(n), g);

    // prove f+g ∈ Ω(g)
    var c2:R0, n2:nat := 1.0, 0;
    forall n:nat | 0 <= n2 <= n
      ensures c2*g(n) <= f(n) + g(n)
    {
      calc {
           c2*g(n); 
        <= f(n) + g(n);        
      }
    }  
    assert bigOmFrom(c2, n2, n => f(n)+g(n), g);
  }  

  // If f ∈ O(g+h) and g ∈ O(h) then f ∈ O(h)
  lemma lem_bigO_sumSimp2(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires f in O(n => g(n)+h(n)) 
    requires g in O(h) 
    ensures  f in O(h) 
  {
    lem_bigO_sumSimp(g, h);
    assert bigO(n => g(n)+h(n), h);
    lem_bigO_trans(f, n => g(n)+h(n), h);
  }

  // Any constant function have constant growth
  lemma lem_bigO_constGrowth(f:nat->R0, a:R0)  
    requires forall n:nat :: f(n) == a
    ensures  f in O(constGrowth())
  {  
    var c:R0, n0:nat := a, 0;
    forall n:nat | 0 <= n0 <= n
      ensures f(n) <= c*constGrowth()(n)
    {
      calc {
           f(n); 
        == a;
        <= a*1.0;      
        == c*constGrowth()(n);         
      }
    }
    assert bigOfrom(c, n0, f, constGrowth());
  }

  /******************************************************************************
    Big O basic properties lifted to sets
  ******************************************************************************/
  // Each result easily follows from it's corresponding non-set lifted property

  // This is lem_bigO_sum lifted to sets
  // If f1 ∈ O(g1) and f2 ∈ O(g2) then O(f1+f2) ⊆ O(g1+g2)
  lemma lem_bigOset_sum(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  O(n => f1(n)+f2(n)) <= O(n => g1(n)+g2(n)) 
  {  
    forall h:nat->R0 | h in O(n => f1(n)+f2(n)) 
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
  lemma lem_bigOset_prod(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in O(g1) 
    requires f2 in O(g2)
    ensures  O(n => f1(n)*f2(n)) <= O(n => g1(n)*g2(n)) 
  {  
    forall h:nat->R0 | h in O(n => f1(n)*f2(n)) 
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
  lemma lem_bigOset_sumSimp(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  O(n => f(n)+g(n)) == O(g)
  {
    // prove O(f+g) ⊆ O(g)
    forall h:nat->R0 | h in O(n => f(n)+g(n)) 
      ensures h in O(g) 
    {
      assert h in O(n => f(n)+g(n));  
      assert (n => f(n)+g(n)) in O(g) 
        by { lem_bigO_sumSimp(f, g); }
      lem_bigO_trans(h, n => f(n)+g(n), g);  
    }    

    // prove O(g) ⊆ O(f+g)
    forall h:nat->R0 | h in O(g)
      ensures h in O(n => f(n)+g(n)) 
    {
      assert h in O(g);  
      assert g in O(n => f(n)+g(n)) 
        by { lem_bigO_sumSimp(f, g); lem_bigTh_sim(n => f(n)+g(n), g); }
      lem_bigO_trans(h, g, n => f(n)+g(n));  
    }     
  }

  /******************************************************************************
    Big Ω basic properties
  ******************************************************************************/

  // Reflexivity
  // f ∈ Ω(f)
  lemma lem_bigOm_refl(f:nat->R0)  
    ensures f in Om(f) 
  {  
    // we show that c=1 and n0=0
    var c:R0, n0:nat := 1.0, 0;
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) >= c*f(n);
    assert bigOmFrom(c, n0, f, f);
  }  

  /******************************************************************************
    Big Θ basic properties
  ******************************************************************************/

  // Reflexivity
  // f ∈ O(f)
  lemma lem_bigTh_refl(f:nat->R0)  
    ensures f in Th(f) 
  {  
    lem_bigO_refl(f); 
    lem_bigOm_refl(f);
  }  

  // Simmetry
  // If f ∈ Θ(g) then g ∈ Θ(f)
  lemma {:axiom} lem_bigTh_sim(f:nat->R0, g:nat->R0)  
    requires f in Th(g) 
    ensures  g in Th(f)

  /******************************************************************************
    Common growth rates comparison
  ******************************************************************************/

  // 1 ∈ O(log_b(n)) 
  lemma lem_bigO_constBigOlog(b:R0)
    requires b > 1.0
    ensures  constGrowth() in O(logGrowth(b)) 
  {
    // we show that c=1 and n0=ceil(b)
    var c:R0, n0:nat := 1.0, ceil(b);
    forall n:nat | 0 <= n0 <= n 
      ensures constGrowth()(n) <= c*logGrowth(b)(n)
    {
      calc {
           constGrowth()(n); 
        == 1.0;
        <= { lem_logGEQone(b, n as R0); }
           1.0*logGrowth(b)(n);      
        == c*logGrowth(b)(n);         
      }
    }
    assert bigOfrom(c, n0, constGrowth(), logGrowth(b));
  } 

  // 1 ∈ O(log2(n)) 
  lemma lem_bigO_constBigOlog2()
    ensures constGrowth() in O(log2Growth()) 
  {
    lem_bigO_constBigOlog(2.0);
    assert constGrowth() in O(logGrowth(2.0));
    lem_funExt(log2Growth(), logGrowth(2.0));
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

  // k >= 1 ==> 1 ∈ O(n^k)  
  lemma lem_bigO_constBigOpoly(k:R0)
    requires k >= 1.0
    ensures  constGrowth() in O(polyGrowth(k)) 
  {
    // Follows from transitivity of 1 ∈ O(log2(n)) and log2(n) ∈ O(n^k)  
    assert constGrowth() in O(log2Growth())  by { lem_bigO_constBigOlog2(); }
    assert log2Growth()  in O(polyGrowth(k)) by { lem_bigO_log2BigOpoly(k); }
    lem_bigO_trans(constGrowth(), log2Growth(), polyGrowth(k));
  } 

  // b >= 2 ==> 1 ∈ O(b^n)  
  lemma lem_bigO_constBigOexp(b:R0)
    requires b >= 2.0
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
    // we show that c=1 and n0=1
    var c:R0, n0:nat := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures log2Growth()(n) <= c*linGrowth()(n)
    {
      calc {      
           log2Growth()(n); 
        == log2(n as real);
        <  { lem_log2NatUpBound(n); }
           (LN.log2(n) + 1) as R0;
        <= { lem_log2nLEQnMinus1(n); }
           ((n - 1) + 1) as R0;   
        == n as R0;   
        <= c*n as R0;
        == { lem_expOne(n as R0); }
           c*exp(n as R0, 1.0);
        == c*linGrowth()(n);
      }
    }
    assert bigOfrom(c, n0, log2Growth(), linGrowth());
  }

  // log2(n+1) ∈ O(n) 
  lemma lem_bigO_logBigOlinV2()
    ensures log2Plus1Growth() in O(linGrowth())
  {
    // we show that c=2 and n0=1
    var c:R0, n0:nat := 2.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures log2Plus1Growth()(n) <= c*linGrowth()(n)
    {
      calc {      
           log2Plus1Growth()(n); 
        == log2((n+1) as real);
        <  { lem_log2NatUpBound(n+1);  }
           (LN.log2(n+1) + 1) as R0;
        <= { lem_log2nPlus1LEQn(n); }
           (n + 1) as R0;   
        <= c*n as R0;
        == { lem_expOne(n as R0); }
           c*exp(n as R0, 1.0);
        == c*linGrowth()(n);
      }
    }
    assert bigOfrom(c, n0, log2Plus1Growth(), linGrowth());    
  }

  // k >= 1 ==> log2(n) ∈ O(n^k) 
  lemma lem_bigO_log2BigOpoly(k:R0)
    requires k >= 1.0
    ensures  log2Growth() in O(polyGrowth(k))
  { 
    // Follows from transitivity of log2(n) ∈ O(n) and n ∈ O(n^k)  
    assert log2Growth() in O(linGrowth())   by { lem_bigO_log2BigOlin(); }
    assert linGrowth()  in O(polyGrowth(k)) by { lem_bigO_linBigOpoly(k); }
    lem_bigO_trans(log2Growth(), linGrowth(), polyGrowth(k));    
  }

  // k >= 1 ==> n ∈ O(n^k) 
  lemma lem_bigO_linBigOpoly(k:R0)
    requires k >= 1.0
    ensures  linGrowth() in O(polyGrowth(k)) 
  { 
    // we show that c=1 and n0=1
    var c:R0, n0:nat := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures linGrowth()(n) <= c*polyGrowth(k)(n)
    {
      calc {      
           linGrowth()(n); 
        == exp(n as R0, 1.0);        
        <= { lem_expMonoIncr(n as R0, 1.0, k); }
           exp(n as R0, k);
        <= c*exp(n as R0, k);
        == c*polyGrowth(k)(n);
      }
    }
    assert bigOfrom(c, n0, linGrowth(), polyGrowth(k));
  }

  // n ∈ O(n^2) 
  lemma lem_bigO_linBigOquad()
    ensures linGrowth() in O(quadGrowth()) 
  {
    lem_bigO_linBigOpoly(2.0);
  }

  // n ∈ O(n^3) 
  lemma lem_bigO_linBigOcubic()
    ensures linGrowth() in O(cubicGrowth()) 
  { 
    lem_bigO_linBigOpoly(3.0);
  }  

  // n^2 ∈ O(2^n)  
  lemma lem_bigO_quadBigOexp()
    ensures quadGrowth() in O(exp2Growth()) 
  {
    // we show that c=1 and n0=4
    var c:R0, n0:nat := 1.0, 4;
    forall n:nat | 0 <= n0 <= n
      ensures quadGrowth()(n) <= c*exp2Growth()(n)
    {
      calc {      
           quadGrowth()(n); 
        == exp(n as R0, 2.0);           
        == { lem_expOverNat(n, 2); }
           EN.exp(n, 2) as real;
        <= { lem_expn2LEQexp2n(n); }  
           EN.exp(2, n) as real; 
        == { lem_expOverNat(2, n); }     
           exp(2.0, n as R0); 
        <= c*exp(2.0, n as R0);
        == c*exp2(n as R0);
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
  lemma lem_bigO_linBigOexp(b:R0)
    requires b >= 2.0
    ensures  linGrowth() in O(expGrowth(b)) 
  { 
    // Follows from transitivity of n ∈ O(2^n) and 2^n ∈ O(b^n)  
    assert linGrowth()  in O(exp2Growth()) by { lem_bigO_linBigOexp2(); }
    assert exp2Growth() in O(expGrowth(b)) by { lem_bigO_exp2BigOexp(b); }
    lem_bigO_trans(linGrowth(), exp2Growth(), expGrowth(b));
  }    

  // b >= 2 ==> 2^n ∈ O(b^n)  
  lemma lem_bigO_exp2BigOexp(b:R0)
    requires b >= 2.0
    ensures  exp2Growth() in O(expGrowth(b))
  {
    // we show that c=1 and n0=1
    var c:R0, n0:nat := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures exp2Growth()(n) <= c*expGrowth(b)(n)
    {
      calc {      
           exp2Growth()(n); 
        == exp2(n as R0);        
        == exp(2.0, n as R0);
        <= { lem_expBaseMonoIncr(n as R0, 2.0, b); }
           exp(b, n as R0);
        <= c*exp(b, n as R0);
        == c*expGrowth(b)(n);
      }
    }
    assert bigOfrom(c, n0, exp2Growth(), expGrowth(b));    
  }

}