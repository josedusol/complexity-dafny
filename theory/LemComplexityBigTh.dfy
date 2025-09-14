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
include "./LemComplexityBigOh.dfy"
include "./LemComplexityBigOm.dfy"

/******************************************************************************
  Lemmas of Big Theta Notation
******************************************************************************/

module LemComplexityBigTh {

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
  import opened LemComplexityBigOh
  import opened LemComplexityBigOm

  /******************************************************************************
    Θ basic properties
  ******************************************************************************/

  // Reflexivity
  // f ∈ Θ(f)
  lemma lem_bigTh_refl(f:nat->R0)  
    ensures f in Th(f) 
  {  
    lem_bigO_refl(f); 
    lem_bigOm_refl(f);
    lem_bigTh_def2IMPdef(f, f);
  }  

  // Symmetry
  // f ∈ Θ(g) ⟹ g ∈ Θ(f)
  lemma lem_bigTh_sym(f:nat->R0, g:nat->R0)  
    requires f in Th(g) 
    ensures  g in Th(f)
  // TODO  

  // Transitivity
  // f ∈ Ω(g) ∧ g ∈ Ω(h) ⟹ f ∈ Ω(h)
  lemma lem_bigTh_trans(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires f in Th(g) 
    requires g in Th(h)  
    ensures  f in Th(h)  
  {
    lem_bigTh_defIMPdef2(f, g);
    lem_bigTh_defIMPdef2(g, h);
    lem_bigO_trans(f, g, h); 
    lem_bigOm_trans(f, g, h);
    lem_bigTh_def2IMPdef(f, h);
  }  

  // Zero function is Θ(0)
  lemma lem_bigTh_zeroGrowth(f:nat->R0)  
    requires forall n:nat :: f(n) == 0.0
    ensures  f in Th(zeroGrowth())
  {  
    var c1:R0, c2:R0, n0:nat := 1.0, 1.0, 0;
    forall n:nat | 0 <= n0 <= n
      ensures c1*zeroGrowth()(n) <= f(n) <= c2*zeroGrowth()(n)
    {
      calc {
           c1*zeroGrowth()(n);
        == c1*0.0;  
        == 0.0;  
        <= f(n); 
        == 0.0;
        <= c2*0.0;      
        == c2*zeroGrowth()(n);         
      }
    }
    assert c1 > 0.0 && c2 > 0.0 && bigThFrom(c1, c2, n0, f, zeroGrowth());
  }

  // Any non-zero constant function is Θ(1)
  lemma lem_bigTh_constGrowth(f:nat->R0, a:R0)  
    requires a > 0.0
    requires forall n:nat :: f(n) == a
    ensures  f in Th(constGrowth())
  {
    var c1:R0, c2:R0, n0:nat := a/2.0, a, 0;
    forall n:nat | 0 <= n0 <= n
      ensures c1*constGrowth()(n) <= f(n) <= c2*constGrowth()(n)
    {
      calc {
           c1*constGrowth()(n);
        == c1*1.0; 
        == a/2.0; 
        <= f(n); 
        == a;
        <= c2*1.0;      
        == c2*constGrowth()(n);         
      }
    }
    assert c1 > 0.0 && c2 > 0.0 && bigThFrom(c1, c2, n0, f, constGrowth());
  }  

  // The base of log doesn't change asymptotics
  // b1,b2 > 0 ⟹ (h ∈ Θ(log_b1) ⟺ h ∈ Θ(log_b2))
  lemma lem_bigTh_logBase(b1:real, b2:real, h:nat->R0)  
    requires b1 > 1.0 && b2 > 1.0
    requires h in Th(logGrowth(b1))
    ensures  h in Th(logGrowth(b2))
  {
    assert A: h in O(logGrowth(b1)) && h in Om(logGrowth(b1))
      by { lem_bigTh_defIMPdef2(h, logGrowth(b1)); }

    assert B: h in O(logGrowth(b2)) 
      by { reveal A; lem_bigO_logBase(b1, b2, h); }

    assert C: h in Om(logGrowth(b2)) 
      by { reveal A; lem_bigOm_logBase(b1, b2, h); }

    assert h in Th(logGrowth(b2)) 
      by { reveal B, C; lem_bigTh_def2IMPdef(h, logGrowth(b2)); }    
  } 

  // b1,b2 > 0 ⟹ Θ(log_b1) = Θ(log_b2)
  lemma lem_bigThSet_logBase(b1:real, b2:real)  
    requires b1 > 1.0 && b2 > 1.0
    ensures  Th(logGrowth(b1)) == Th(logGrowth(b2))
  {
    forall h:nat->R0
      ensures h in Th(logGrowth(b1)) <==> h in Th(logGrowth(b2))
    {
      assert h in Th(logGrowth(b1)) ==> h in Th(logGrowth(b2)) by { 
        if h in Th(logGrowth(b1)) {
          lem_bigTh_logBase(b1, b2, h); 
        }
      }
      assert h in Th(logGrowth(b2)) ==> h in Th(logGrowth(b1)) by { 
        if h in Th(logGrowth(b2)) {
          lem_bigTh_logBase(b2, b1, h); 
        }
      }      
    }
  }

  // Θ(f) = Θ(g) ⟹ f ∈ Θ(g) ∧ g ∈ Θ(f)
  lemma lem_bigThSet_mutualInc(f:nat->R0, g:nat->R0)  
    requires Th(f) == Th(g)
    ensures  f in Th(g) && g in Th(f)
  { 
    assert f in Th(f) by { lem_bigTh_refl(f); }
    assert g in Th(g) by { lem_bigTh_refl(g); }
  }

  // Congruence of membership with respect to equality
  // Θ(f) = Θ(g) ∧ f ∈ Θ(h) ⟹ g ∈ Θ(h)
  lemma lem_bigThset_congEq(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires Th(f) == Th(g)
    requires f in Th(h)
    ensures  g in Th(h) 
  {
    lem_bigThSet_mutualInc(f, g);
    assert g in Th(f);
    assert f in Th(h);
    lem_bigTh_trans(g, f, h);
  }

  /******************************************************************************
    bigTh and bigTh2 are equivalent definitions of Big Θ 
  ******************************************************************************/

  lemma lem_bigTh_defEQdef2(f:nat->R0, g:nat->R0)  
    ensures bigTh(f, g) <==> bigTh2(f, g)
  {
    assert bigTh(f, g) ==> bigTh2(f, g) by {
      if bigTh(f, g) {
        lem_bigTh_defIMPdef2(f, g);
      }      
    }
    assert bigTh2(f, g) ==> bigTh(f, g) by {
      if bigTh2(f, g) {
        lem_bigTh_def2IMPdef(f, g);
      }      
    }
  }

  lemma lem_bigTh_defIMPdef2(f:nat->R0, g:nat->R0)  
    requires bigTh(f, g) 
    ensures  bigTh2(f, g)
  {
    var c1:R0, c2:R0, n0:nat :| c1 > 0.0 && c2 > 0.0 && bigThFrom(c1, c2, n0, f, g); 
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

  lemma lem_bigTh_def2IMPdef(f:nat->R0, g:nat->R0)  
    requires bigTh2(f, g) 
    ensures  bigTh(f, g)
  {
    var c1:R0, n0_1:nat :| c1 > 0.0 && bigOmFrom(c1, n0_1, f, g) ; 
    assert H1: forall n:nat :: 0 <= n0_1 <= n ==> c1*g(n) <= f(n);

    var c2:R0, n0_2:nat :| c2 > 0.0 && bigOfrom(c2, n0_2, f, g) ; 
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

  // A stronger way to conclude a program counter t is Θ(g) for input size n
  lemma lem_bigTh_tIsBigTh2(n:nat, t:R0, g:nat->R0)  
    requires exists f:nat->R0 :: f(n) == t && bigTh(f, g)
    ensures  tIsBigTh(n, t, g) 
  {
    var f:nat->R0 :| f(n) == t && bigTh(f, g);
    lem_bigTh_defIMPdef2(f, g);
  }

  /******************************************************************************
    Mixed O/Θ/Ω properties
  ******************************************************************************/

  // f ∈ O(g) ⟹ f+g ∈ Θ(g)
  lemma lem_asymp_sumSimp(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  (n => f(n)+g(n)) in Th(g)    
  {
    lem_bigO_sumSimp(f, g);
    lem_bigOm_sumSimp(f, g);
    lem_bigTh_def2IMPdef(n => f(n)+g(n), g);
  }  

  // f ∈ O(g) ⟹ Θ(f+g) = Θ(g)
  lemma lem_asympSet_sumSimp(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  Th(n => f(n)+g(n)) == Th(g) 
  {
    // prove Θ(f+g) ⊆ Θ(g)
    forall h:nat->R0 | h in Th(n => f(n)+g(n)) 
      ensures h in Th(g) 
    {
      assert h in Th(n => f(n)+g(n));  
      assert (n => f(n)+g(n)) in Th(g) 
        by { lem_asymp_sumSimp(f, g); }
      lem_bigTh_trans(h, n => f(n)+g(n), g);  
    }    
    
    // prove Θ(g) ⊆ Θ(f+g)
    forall h:nat->R0 | h in Th(g)
      ensures h in Th(n => f(n)+g(n)) 
    {
      assert h in Th(g);  
      assert g in Th(n => f(n)+g(n))
        by { lem_asymp_sumSimp(f, g); lem_bigTh_sym(n => f(n)+g(n), g); }
      lem_bigTh_trans(h, g, n => f(n)+g(n));   
    }  
  } 

  //   f(n) <= up(n) eventually ∧ lo(n) <= f(n) eventually 
  // ∧ up ∈ O(h) ∧ lo ∈ Ω(h) ⟹ f ∈ Θ(h)
  lemma lem_asymp_sandwich(f:nat->R0, lo:nat->R0, up:nat->R0, g:nat->R0, n1:nat, n2:nat)  
    requires forall n:nat :: n >= n1 ==> lo(n) <= f(n)
    requires forall n:nat :: n >= n2 ==> f(n)  <= up(n)
    requires lo in Om(g)
    requires up in O(g)
    ensures  f  in Th(g)
  {
    assert f in Om(g) by {
      lem_bigOm_LEQupwardClosure(f, lo, g, n1);
    }
    assert f in O(g) by {
      lem_bigO_LEQdownwardClosure(f, up, g, n2);
    }    
    assert f in Th(g) by {
      lem_bigTh_defEQdef2(f, g);
    }
  }

}