include "./math/ExpNat.dfy"
include "./math/ExpReal.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemBoundsNat.dfy"
include "./math/LemFunction.dfy"
include "./math/Log2Nat.dfy"
include "./math/Log2Real.dfy"
include "./math/LogReal.dfy"
include "./math/MaxMin.dfy"
include "./math/TypeR0.dfy"
include "./Complexity.dfy"

/******************************************************************************
  Lemmas of Big Oh Notation
******************************************************************************/

module LemComplexityBigOh {

  import EN = ExpNat
  import opened ExpReal
  import opened FloorCeil   
  import opened LemBoundsNat
  import opened LemFunction
  import LN = Log2Nat
  import opened Log2Real
  import opened LogReal
  import opened MaxMin
  import opened TypeR0 
  import opened Complexity

  /******************************************************************************
    O basic properties
  ******************************************************************************/

  // Reflexivity
  // f ∈ O(f)
  lemma lem_bigO_refl(f:nat->R0)  
    ensures f in O(f) 
  {  
    var c:R0, n0:nat := 1.0, 0;
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*f(n);
    assert bigOfrom(c, n0, f, f);
  }

  // Transitivity
  // f ∈ O(g) ∧ g ∈ O(h) ⟹ f ∈ O(h)
  lemma lem_bigO_trans(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires f in O(g) 
    requires g in O(h)  
    ensures  f in O(h)  
  {  
    var c1:R0, n1:nat :| c1 > 0.0 && bigOfrom(c1, n1, f, g);  
    assert forall n:nat :: 0 <= n1 <= n ==> f(n) <= c1*g(n);
    var c2:R0, n2:nat :| c2 > 0.0 && bigOfrom(c2, n2, g, h);  
    assert forall n:nat :: 0 <= n2 <= n ==> g(n) <= c2*h(n);   
    
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

  // f ∈ O(g) ∧ a > 0 ⟹ a*f ∈ O(g)
  lemma lem_bigO_constFactor(f:nat->R0, g:nat->R0, a:R0)
    requires f in O(g) 
    requires a > 0.0 
    ensures  (n => a*f(n)) in O(g) 
  {  
    var c:R0, n0:nat :| c > 0.0 && bigOfrom(c, n0, f, g);  
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);
    
    // we show that c'=a*c and n0'=n0
    assert forall n:nat :: 0 <= n0 <= n ==> a*f(n) <= (a*c)*g(n);
    assert bigOfrom(a*c, n0, n => a*f(n), g);
  }

  // f1 ∈ O(g1) ∧ f2 ∈ O(g2) ⟹ f1+f2 ∈ O(g1+g2)
  lemma lem_bigO_sum(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  (n => f1(n)+f2(n)) in O(n => g1(n)+g2(n)) 
  {  
    var c1:R0, n1:nat :| c1 > 0.0 && bigOfrom(c1, n1, f1, g1);  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> f1(n) <= c1*g1(n);
    var c2:R0, n2:nat :| c2 > 0.0 && bigOfrom(c2, n2, f2, g2);  
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

  // f1 ∈ O(g1) ∧ f2 ∈ O(g2) ⟹ f1*f2 ∈ O(g1*g2)
  lemma lem_bigO_prod(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  (n => f1(n)*f2(n)) in O(n => g1(n)*g2(n))  
  {  
    var c1:R0, n1:nat :| c1 > 0.0 && bigOfrom(c1, n1, f1, g1);  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> f1(n) <= c1*g1(n);
    var c2:R0, n2:nat :| c2 > 0.0 && bigOfrom(c2, n2, f2, g2);  
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

  // f ∈ O(g) ⟹ f+g ∈ O(g)
  lemma lem_bigO_sumSimp(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  (n => f(n)+g(n)) in O(g)  
  {
    var c:R0, n0:nat :| c > 0.0 && bigOfrom(c, n0, f, g);  
    assert H1: forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);

    // prove f+g ∈ O(g)
    var c1:R0, n1:nat := c + 1.0, n0;
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
    assert c1 > 0.0 && bigOfrom(c1, n1, n => f(n)+g(n), g);
  }

  // f ∈ O(g) ⟹ g ∈ O(f+g)
  lemma lem_bigO_sumSynth(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  g in O(n => f(n)+g(n))  
  {
    var c1:R0, n1:nat := 1.0, 0;
    forall n:nat | 0 <= n1 <= n
      ensures g(n) <= c1*(f(n) + g(n))
    {
      calc {
           g(n);       
        <= f(n) + g(n);
        <= c1*(f(n) + g(n));
      }
    }  
    assert c1 > 0.0 && bigOfrom(c1, n1, g, n => f(n)+g(n));
  }  

  // f ∈ O(g+h) ∧ g ∈ O(h) ⟹ f ∈ O(h)
  lemma lem_bigO_sumSimp2(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires f in O(n => g(n)+h(n)) 
    requires g in O(h) 
    ensures  f in O(h) 
  {
    lem_bigO_sumSimp(g, h);
    assert bigO(n => g(n)+h(n), h);
    lem_bigO_trans(f, n => g(n)+h(n), h);
  }
  
  // Any constant function is O(1)
  lemma lem_bigO_constGrowth(f:nat->R0, a:R0)  
    requires forall n:nat :: f(n) == a
    ensures  f in O(constGrowth())
  {  
    var c:R0, n0:nat := a+1.0, 0;
    forall n:nat | 0 <= n0 <= n
      ensures f(n) <= c*constGrowth()(n)
    {
      calc {
           f(n); 
        == a;
        <= (a+1.0)*1.0;      
        == c*constGrowth()(n);         
      }
    }
    assert bigOfrom(c, n0, f, constGrowth());
  }

  // The base of log doesn't change asymptotics
  // b1,b2 > 0 ⟹ (h ∈ O(log_b1) ⟺ h ∈ O(log_b2))
  lemma lem_bigO_logBase(b1:real, b2:real, h:nat->R0)  
    requires b1 > 1.0 && b2 > 1.0
    requires h in O(logGrowth(b1))
    ensures  h in O(logGrowth(b2))
  {
    var c1:R0, n0:nat :| c1 > 0.0 && bigOfrom(c1, n0, h, logGrowth(b1));
    assert H1: forall n:nat :: 0 <= n0 <= n ==> h(n) <= c1*logGrowth(b1)(n); 

    lem_log_NonNegative(b2, b1);
    var G:R0 := log(b2, b1); 
    assert G > 0.0 by { lem_log_Positive(b2, b1); }
    var c1':R0, n0':nat := c1/G, n0+1;
    forall n:nat | 0 <= n0' <= n
      ensures h(n) <= c1'*logGrowth(b2)(n)
    {
      calc {
           h(n);
        <= { reveal H1; }
           c1*(log(b1, n as R0));
        == { lem_log_ChangeOfBase(b1, b2, n as R0); }
           c1*(log(b2, n as R0)/G);  
        == c1'*log(b2, n as R0);   
        == c1'*logGrowth(b2)(n);      
      }
    }
    assert c1' > 0.0 && bigOfrom(c1', n0', h, logGrowth(b2));
  } 

  // Downward closure wrto <=
  // f(n) <= up(n) eventually ∧ up ∈ O(h) ⟹ f ∈ O(h)
  lemma lem_bigO_LEQdownwardClosure(f:nat->R0, up:nat->R0, h:nat->R0, n1:nat)  
    requires forall n:nat :: n >= n1 ==> f(n) <= up(n)
    requires up in O(h)
    ensures  f  in O(h)
  {  
    var c2:R0, n2:nat :| c2 > 0.0 && bigOfrom(c2, n2, up, h);  
    assert H1: forall n:nat :: 0 <= n2 <= n ==> up(n) <= c2*h(n);

    var c:R0, n0:nat := c2, max(n1, n2);
    forall n:nat | 0 <= n0 <= n
      ensures f(n) <= c*h(n)
    {
      calc {
           f(n); 
        <= up(n);
        <= c2*h(n);         
      }
      assert f(n) <= c2*h(n);
    }
    assert bigOfrom(c, n0, f, h);
  }

  /******************************************************************************
    O basic properties lifted to sets
  ******************************************************************************/
  // Each result follows from it's corresponding non-set lifted property

  // This is lem_bigO_sum lifted to sets
  // f1 ∈ O(g1) ∧ f2 ∈ O(g2) ==> O(f1+f2) ⊆ O(g1+g2)
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
  // f1 ∈ O(g1) ∧ f2 ∈ O(g2) ==> O(f1*f2) ⊆ O(g1*g2)
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

  // b1,b2 > 0 ⟹ O(log_b1) = O(log_b2)
  lemma lem_bigOset_logBase(b1:real, b2:real)  
    requires b1 > 1.0 && b2 > 1.0
    ensures  O(logGrowth(b1)) == O(logGrowth(b2))
  {
    forall h:nat->R0
      ensures h in O(logGrowth(b1)) <==> h in O(logGrowth(b2))
    {
      assert h in O(logGrowth(b1)) ==> h in O(logGrowth(b2)) by { 
        if h in O(logGrowth(b1)) {
          lem_bigO_logBase(b1, b2, h); 
        }
      }
      assert h in O(logGrowth(b2)) ==> h in O(logGrowth(b1)) by { 
        if h in O(logGrowth(b2)) {
          lem_bigO_logBase(b2, b1, h); 
        }
      }      
    }
  }

  // f ∈ O(g) ⟹ O(f+g) = O(g)
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
        by { lem_bigO_sumSynth(f, g); }
      lem_bigO_trans(h, g, n => f(n)+g(n));  
    }      
  }

  // O(f) = O(g) ⟹ f ∈ O(g) ∧ g ∈ O(f)
  lemma lem_bigOset_mutualInc(f:nat->R0, g:nat->R0)  
    requires O(f) == O(g)
    ensures  f in O(g) && g in O(f)
  { 
    assert f in O(f) by { lem_bigO_refl(f); }
    assert g in O(g) by { lem_bigO_refl(g); }
  }

  // Congruence of membership with respect to equality
  // O(f) = O(g) ∧ f ∈ O(h) ⟹ g ∈ O(h)
  lemma lem_bigOset_congEq(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires O(f) == O(g)
    requires f in O(h)
    ensures  g in O(h) 
  {
    lem_bigOset_mutualInc(f, g);
    assert g in O(f);
    assert f in O(h);
    lem_bigO_trans(g, f, h);
  }

  /******************************************************************************
    Comparison of common growth rates according to O
  ******************************************************************************/

  // 0 ∈ O(f) 
  lemma lem_bigO_zeroBigOany(f:nat->R0)
    ensures zeroGrowth() in O(f) 
  {
    var c:R0, n0:nat := 1.0, 0;
    forall n:nat | 0 <= n0 <= n 
      ensures zeroGrowth()(n) <= c*f(n)
    {
      calc {
           zeroGrowth()(n);
        == 0.0;
        <= 1.0*f(n);             
      }
    }
    assert c > 0.0 && bigOfrom(c, n0, zeroGrowth(), f);
  } 

  // 0 ∈ O(1) 
  lemma lem_bigO_zeroBigOconst()
    ensures zeroGrowth() in O(constGrowth()) 
  {
    lem_bigO_zeroBigOany(constGrowth());
  }   

  // 1 ∈ O(log_b) 
  lemma lem_bigO_constBigOlog(b:R0)
    requires b > 1.0
    ensures  constGrowth() in O(logGrowth(b))
  {
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

  // 1 ∈ O(log2) 
  lemma lem_bigO_constBigOlog2()
    ensures constGrowth() in O(log2Growth()) 
  {
    lem_bigO_constBigOlog(2.0);
    assert constGrowth() in O(logGrowth(2.0));
    lem_fun_Ext(log2Growth(), logGrowth(2.0)) 
      by { reveal log2(); }
  }    

  // 1 ∈ O(n) 
  lemma lem_bigO_constBigOlin()
    ensures constGrowth() in O(linGrowth()) 
  {
    // From transitivity of 1 ∈ O(log2) and log2 ∈ O(n)  
    assert constGrowth() in O(log2Growth()) by { lem_bigO_constBigOlog2(); }
    assert log2Growth()  in O(linGrowth())  by { lem_bigO_log2BigOlin(); }
    lem_bigO_trans(constGrowth(), log2Growth(), linGrowth());
  }    

  // k >= 1 ⟹ 1 ∈ O(n^k)  
  lemma lem_bigO_constBigOpoly(k:R0)
    requires k >= 1.0
    ensures  constGrowth() in O(polyGrowth(k)) 
  {
    // From transitivity of 1 ∈ O(log2) and log2 ∈ O(n^k)  
    assert constGrowth() in O(log2Growth())  by { lem_bigO_constBigOlog2(); }
    assert log2Growth()  in O(polyGrowth(k)) by { lem_bigO_log2BigOpoly(k); }
    lem_bigO_trans(constGrowth(), log2Growth(), polyGrowth(k));
  } 

  // b >= 2 ⟹ 1 ∈ O(b^n)  
  lemma lem_bigO_constBigOexp(b:R0)
    requires b >= 2.0
    ensures  constGrowth() in O(expGrowth(b)) 
  {
    // From transitivity of 1 ∈ O(n) and n ∈ O(b^n)  
    assert constGrowth() in O(linGrowth())  by { lem_bigO_constBigOlin(); }
    assert linGrowth()   in O(expGrowth(b)) by { lem_bigO_linBigOexp(b); }
    lem_bigO_trans(constGrowth(), linGrowth(), expGrowth(b));
  }   

  // log2 ∈ O(n) 
  lemma lem_bigO_log2BigOlin()
    ensures log2Growth() in O(linGrowth()) 
  {
    var c:R0, n0:nat := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures log2Growth()(n) <= c*linGrowth()(n)
    {
      calc {      
           log2Growth()(n); 
        == log2(n as real);
        <  { lem_log2_NatUpBound(n); }
           (LN.log2(n) + 1) as R0;
        <= { lem_log2nLEQnMinus1(n); }
           ((n - 1) + 1) as R0;   
        == n as R0;   
        <= c*n as R0;
        == c*linGrowth()(n);
      }
    }
    assert bigOfrom(c, n0, log2Growth(), linGrowth());
  }

  // log_b ∈ O(n) 
  lemma lem_bigO_logBigOlin(b:R0)
    requires b > 1.0
    ensures logGrowth(b) in O(linGrowth()) 
  {  
    lem_bigOset_logBase(2.0, b);  
    lem_bigO_log2BigOlin();   
    lem_fun_Ext(log2Growth(), logGrowth(2.0)) by { reveal log2(); }

    lem_bigOset_congEq(logGrowth(2.0), logGrowth(b), linGrowth());
  }

  // log2(n+1) ∈ O(n) 
  lemma lem_bigO_log2PlusOneBigOlin()
    ensures log2Plus1Growth() in O(linGrowth())
  {
    var c:R0, n0:nat := 2.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures log2Plus1Growth()(n) <= c*linGrowth()(n)
    {
      calc {      
           log2Plus1Growth()(n); 
        == log2((n+1) as real);
        <  { lem_log2_NatUpBound(n+1);  }
           (LN.log2(n+1) + 1) as R0;
        <= { lem_log2nPlus1LEQn(n); }
           (n + 1) as R0;   
        <= c*n as R0;
        == c*linGrowth()(n);
      }
    }
    assert bigOfrom(c, n0, log2Plus1Growth(), linGrowth());    
  }

  // k >= 1 ⟹ log2 ∈ O(n^k) 
  lemma lem_bigO_log2BigOpoly(k:R0)
    requires k >= 1.0
    ensures  log2Growth() in O(polyGrowth(k))
  { 
    // From transitivity of log2 ∈ O(n) and n ∈ O(n^k)  
    assert log2Growth() in O(linGrowth())   by { lem_bigO_log2BigOlin(); }
    assert linGrowth()  in O(polyGrowth(k)) by { lem_bigO_linBigOpoly(k); }
    lem_bigO_trans(log2Growth(), linGrowth(), polyGrowth(k));    
  }

  // b > 1 ∧ k >= 1 ⟹ log_b ∈ O(n^k) 
  lemma lem_bigO_logBigOpoly(b:R0, k:R0)
    requires b > 1.0 && k >= 1.0
    ensures logGrowth(b) in O(polyGrowth(k))
  {  
    // From transitivity of log_b ∈ O(n) and n ∈ O(n^k)  
    assert logGrowth(b) in O(linGrowth())   by { lem_bigO_logBigOlin(b); }
    assert linGrowth()  in O(polyGrowth(k)) by { lem_bigO_linBigOpoly(k); }
    lem_bigO_trans(logGrowth(b), linGrowth(), polyGrowth(k));    
  }  

  // k >= 1 ⟹ n ∈ O(n^k) 
  lemma lem_bigO_linBigOpoly(k:R0)
    requires k >= 1.0
    ensures  linGrowth() in O(polyGrowth(k)) 
  { 
    var c:R0, n0:nat := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures linGrowth()(n) <= c*polyGrowth(k)(n)
    {
      calc {      
           linGrowth()(n); 
        == n as R0;  
        == { lem_exp_Pow1(n as R0); }
           exp(n as R0, 1.0);
        <= { lem_exp_MonoIncr(n as R0, 1.0, k); }
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
    lem_exp_Pow2Auto();
    lem_fun_Ext((n:nat) => exp(n as R0, 2.0), (n:nat) => (n*n) as R0);
  }

  // n ∈ O(n^3) 
  lemma lem_bigO_linBigOcubic()
    ensures linGrowth() in O(cubicGrowth()) 
  { 
    lem_bigO_linBigOpoly(3.0);
    lem_exp_Pow3Auto();
    lem_fun_Ext((n:nat) => exp(n as R0, 3.0), (n:nat) => (n*n*n) as R0);    
  }  

  // n^2 ∈ O(2^n)  
  lemma lem_bigO_quadBigOexp()
    ensures quadGrowth() in O(exp2Growth()) 
  {
    var c:R0, n0:nat := 1.0, 4;
    forall n:nat | 0 <= n0 <= n
      ensures quadGrowth()(n) <= c*exp2Growth()(n)
    {
      calc {      
           quadGrowth()(n); 
        == (n*n) as R0;
        == { lem_exp_Pow2(n as R0); }
           exp(n as R0, 2.0);          
        == { lem_exp_OverNat(n, 2); }
           EN.exp(n, 2) as real;
        <= { lem_expn2LEQexp2n(n); }  
           EN.exp(2, n) as real; 
        == { lem_exp_OverNat(2, n); }     
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
    // From transitivity of n ∈ O(n^2) and n^2 ∈ O(2^n)  
    assert linGrowth()  in O(quadGrowth()) by { lem_bigO_linBigOquad(); }
    assert quadGrowth() in O(exp2Growth()) by { lem_bigO_quadBigOexp(); }
    lem_bigO_trans(linGrowth(), quadGrowth(), exp2Growth());
  }

  // n ∈ O(b^n)  
  lemma lem_bigO_linBigOexp(b:R0)
    requires b >= 2.0
    ensures  linGrowth() in O(expGrowth(b)) 
  { 
    // From transitivity of n ∈ O(2^n) and 2^n ∈ O(b^n)  
    assert linGrowth()  in O(exp2Growth()) by { lem_bigO_linBigOexp2(); }
    assert exp2Growth() in O(expGrowth(b)) by { lem_bigO_exp2BigOexp(b); }
    lem_bigO_trans(linGrowth(), exp2Growth(), expGrowth(b));
  }    

  // k >= 0 ⟹ n^k ∈ O(2^n)  
  lemma lem_bigO_polyBigOexp2(k:R0)
    requires k >= 0.0
    ensures  polyGrowth(k) in O(exp2Growth())
  // TODO

  // b >= 2 ⟹ 2^n ∈ O(b^n)  
  lemma lem_bigO_exp2BigOexp(b:R0)
    requires b >= 2.0
    ensures  exp2Growth() in O(expGrowth(b))
  {
    var c:R0, n0:nat := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures exp2Growth()(n) <= c*expGrowth(b)(n)
    {
      calc {      
           exp2Growth()(n); 
        == exp2(n as R0);        
        == exp(2.0, n as R0);
        <= { lem_exp_BaseMonoIncr(n as R0, 2.0, b); }
           exp(b, n as R0);
        <= c*exp(b, n as R0);
        == c*expGrowth(b)(n);
      }
    }
    assert bigOfrom(c, n0, exp2Growth(), expGrowth(b));    
  }

  // k >= 0 ∧ b >= 2 ⟹ n^k ∈ O(b^n)  
  lemma lem_bigO_polyBigOexp(k:R0, b:R0)
    requires k >= 0.0 && b >= 2.0
    ensures  polyGrowth(k) in O(expGrowth(b))
  {
    // From transitivity of n^k ∈ O(2^n) and 2^n ∈ O(b^n)  
    assert polyGrowth(k) in O(exp2Growth()) by { lem_bigO_polyBigOexp2(k); }
    assert exp2Growth()  in O(expGrowth(b)) by { lem_bigO_exp2BigOexp(b); }
    lem_bigO_trans(polyGrowth(k), exp2Growth(), expGrowth(b));
  }

  /******************************************************************************
    Inclusion hierarchy: bigger growth functions contain smaller-growth functions.

      O(0) ⊆ O(1) ⊆ O(log_b)
                  ⊆ O(n^2) ⊆ O(n^3) ⊆ ... ⊆ O(n^k) 
                  ⊆ O(2^n) ⊆ O(3^n) ⊆ ... ⊆ O(b^n) 

    Proving O(f) ⊆ O(g) amounts to proving f ∈ O(g) and using transitivity.               
  ******************************************************************************/

  // O(0) ⊆ O(1) 
  lemma lem_bigOset_zeroLEQconst(f:nat->R0)
    ensures O(zeroGrowth()) <= O(constGrowth()) 
  {
    forall h:nat->R0 | h in O(zeroGrowth()) 
      ensures h in O(constGrowth()) 
    {
      calc {
            h in O(zeroGrowth());
        ==> { lem_bigO_zeroBigOconst(); 
              lem_bigO_trans(h, zeroGrowth(), constGrowth()); }
            h in O(constGrowth());
      }
    } 
  }

  // O(1) ⊆ O(log_b) 
  lemma lem_bigOset_constLEQlog(b:R0)
    requires b > 1.0
    ensures O(constGrowth()) <= O(logGrowth(b)) 
  {
    forall h:nat->R0 | h in O(constGrowth()) 
      ensures h in O(logGrowth(b)) 
    {
      calc {
            h in O(constGrowth());
        ==> { lem_bigO_constBigOlog(b); 
              lem_bigO_trans(h, constGrowth(), logGrowth(b)); }
            h in O(logGrowth(b));
      }
    } 
  }  

  // O(log_b) ⊆ O(n^k) 
  lemma lem_bigOset_logLEQpoly(b:R0, k:R0)
    requires b > 1.0 && k >= 1.0
    ensures O(logGrowth(b)) <= O(polyGrowth(k)) 
  {
    forall h:nat->R0 | h in O(logGrowth(b)) 
      ensures h in O(polyGrowth(k)) 
    { 
      calc {
            h in O(logGrowth(b));
        ==> { lem_bigO_logBigOpoly(b, k); 
              lem_bigO_trans(h, logGrowth(b), polyGrowth(k)); }
            h in O(polyGrowth(k));
      }
    } 
  }  

  // O(n^k) ⊆ O(b^n) 
  lemma lem_bigOset_polyLEQexp(k:R0, b:R0)
    requires k >= 0.0 && b >= 2.0
    ensures O(polyGrowth(k)) <= O(expGrowth(b)) 
  {
    forall h:nat->R0 | h in O(polyGrowth(k)) 
      ensures h in O(expGrowth(b)) 
    { 
      calc { 
            h in O(polyGrowth(k));
        ==> { lem_bigO_polyBigOexp(k, b); 
              lem_bigO_trans(h, polyGrowth(k), expGrowth(b)); }
            h in O(expGrowth(b));
      }
    } 
  }  

}