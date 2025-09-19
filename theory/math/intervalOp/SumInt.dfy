include "../Function.dfy"
include "../LemFunction.dfy"
include "./IntervalSumInt.dfy"

/******************************************************************************
  Sum over integer intervals and integer codomain
******************************************************************************/

module SumInt {
 
  import opened Function  
  import opened LemFunction  
  import ISN = IntervalSumInt

  // Σ_{k=a}^{b}f(k) = ⊗_{k=a}^{b}f(k)
  ghost function sum(a:int, b:int, f:int-->int): int
    requires forall k :: a <= k <= b ==> f.requires(k)
  {
    ISN.bigOp(a, b, f)
  } 

  // a <= b ∧ (∀ k : a<=k<=b : f(k) > 0) ⟹ Σ_{k=a}^{b}f(k) > 0
  lemma {:induction false} lem_Positive(a:int, b:int, f:int->int)
    requires a <= b
    requires forall k :: a <= k <= b ==> f(k) > 0
    ensures  sum(a, b, f) > 0
    decreases b - a
  { 
    if a == b {   
      // BC: a = b
      calc {
           sum(b, b, f);
        == { ISN.lem_SplitUnit(b, b, f); reveal sum(); }
           f(b);
        >  0;
      }
    } else {
      // Step. a < b
      //   IH: Σ(a+1, b, f) > 0
      //    T: Σ(a, b, f)   > 0
      calc {  
           sum(a, b, f);
        == { ISN.lem_SplitFirst(a, b, f); } 
           f(a) + sum(a+1, b, f);
        >  0 + sum(a+1, b, f);
        > { lem_Positive(a+1, b, f); }  // by IH
           0 + 0;
        == 0;           
      }
    }    
  }

  // (∀ k : a<=k<=b : f(k) >= 0) ⟹ Σ_{k=a}^{b}f(k) >= 0
  lemma {:induction false} lem_NonNegative(a:int, b:int, f:int->int)
    requires a <= b+1
    requires forall k :: a <= k <= b ==> f(k) >= 0
    ensures  sum(a, b, f) >= 0
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a = b+1
      calc {
           sum(b+1, b, f);
        == { ISN.lem_BaseCase(b+1, b, f); }
           0;
      }
    } else {
      // Step. a <= b
      //   IH: Σ(a+1, b, f) >= 0
      //    T: Σ(a, b, f)   >= 0
      calc {  
           sum(a, b, f);
        == { ISN.lem_SplitFirst(a, b, f); } 
           f(a) + sum(a+1, b, f);
        >= 0 + sum(a+1, b, f);
        >= { lem_NonNegative(a+1, b, f); }  // by IH
           0 + 0;
        == 0;           
      }
    }    
  }

  // i <= j+1 ⟹ c*Σ_{k=i}^{j}f(k) = Σ_{k=i}^{j}c*f(k)
  lemma {:induction false} lem_LinearityConst(a:int, b:int, c:int, f:int->int)
    requires a <= b+1
    ensures  c*sum(a, b, f) == sum(a, b, k => c*f(k))
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           c*sum(b+1, b, f);
        == { ISN.lem_BaseCase(b+1, b, f); }
           0;
        == { ISN.lem_BaseCase(b+1, b, k => c*f(k)); }
           sum(b+1, b, k => c*f(k));       
      }
    } else {  
      // Step. a <= b
      //   IH: c*Σ(a+1, b, f) = c*Σ(a+1, b, k => c*f(k))
      //    T: c*Σ(a, b, f)   = c*Σ(a, b, k => f(k))
      calc {  
           c*sum(a, b, f);
        == { ISN.lem_SplitFirst(a, b, f); } 
           c*(f(a) + sum(a+1, b, f));
        == c*f(a) + c*sum(a+1, b, f);         
        == { lem_LinearityConst(a+1, b, c, f); }  // by IH
           c*f(a) + sum(a+1, b, k => c*f(k)); 
        == (k => c*f(k))(a) + sum(a+1, b, k => c*f(k));
        == { ISN.lem_SplitFirst(a, b, k => c*f(k)); } 
           sum(a, b, k => c*f(k));           
      } 
    }  
  }

  // a <= b+1 ⟹ Σ_{k=a}^{b}c = c*(b - a + 1)
  lemma {:induction false} lem_Const(a:int, b:int, c:int)
    requires a <= b+1
    ensures  sum(a, b, k => c) == c * (b - a + 1)
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           sum(b+1, b, k => c); 
        == { ISN.lem_BaseCase(b+1, b, k => c); } 
           0; 
        == (b - (b+1) + 1);
      }
    } else {  
      // Step. a <= b
      //   IH: Σ(a+1, b, k => c) = c*(b - (a+1) + 1) = c*(b - a)
      //    T: Σ(a, b, k => c)   = c*(b - a + 1) 
      calc {  
           sum(a, b, k => c);
        == { ISN.lem_SplitFirst(a, b, k => c); }
           c + sum(a+1, b, k => c);
        == { lem_Const(a+1, b, c); }  // by IH
           (c + c* (b - (a+1) + 1) );
        == c + c*((b - a));      
        == c * (b - a + 1);             
      }
    }
  }

  lemma lem_ConstAuto(a:int, b:int)
    requires a <= b+1
    ensures  forall c:int :: sum(a, b, k => c) == c * (b - a + 1)
  { 
    forall c:int
      ensures sum(a, b, k => c) == c * (b - a + 1)
    {
      lem_Const(a, b, c);
    }
  } 

  // a <= b+1 ⟹ Σ_{k=a}^{b}k = (b*(b+1) + a*(1-a))/2 
  lemma {:induction false} lem_Interval(a:int, b:int)
    requires a <= b+1 
    decreases b - a
    ensures sum(a, b, k => k) == (b*(b+1) + a*(1-a)) / 2
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           sum(b+1, b, k => k);
        == { ISN.lem_BaseCase(b+1, b, k => k); }
           0;
        == (b*(b+1) + ((b+1))*(1-((b+1)))) / 2;
      }
    } else {  
      // Step. a <= b
      //   IH: Σ(a+1, b, K => k) = (b*(b+1) + (a+1)*(1-(a+1)))/2 
      //    T: Σ(a, b, k => k)   = (b*(b+1) + a*(1-a))/2 
      calc {  
           sum(a, b, k => k);
        == { ISN.lem_SplitFirst(a, b, k => k); }
           a + sum(a+1, b, k => k);
        == { lem_Interval(a+1, b); }  // by IH
           a + (b*(b+1) + (a+1)*(1-(a+1))) / 2;
        == (b*(b+1) + a*(1-a)) / 2;            
      }
    } 
  }

  // Pointwise strict inequalities can be lifted to strict inequality of folded result
  // a <= b ∧  (∀ k : a<=k<=b : f(k) < g(k)) 
  //        ⟹ Σ_{k=a}^{b}f < Σ_{k=a}^{b}g
  lemma {:induction false} lem_StrictIncr(a:int, b:int, f:int->int, g:int->int)
    requires a <= b
    requires forall k:int :: a<=k<=b ==> f(k) < g(k)
    ensures sum(a, b, f) < sum(a, b, g)

  // Following sum lemmas are only stated for integer sum

  // Σ_{k=1}^{n}k = (n*(n+1))/2 
  lemma lem_Triangle(n:nat)
    ensures sum(1, n, k => k) == (n*(n+1))/2
  {
    lem_Interval(1, n);
  }

  // a <= b+1 ⟹ Σ_{k=a}^{b}(b-k+a) = Σ_{k=a}^{b}k
  lemma {:axiom} lem_RevIndex(a:int, b:int)
    requires a <= b+1
    ensures  sum(a, b, k => b-k+a) == sum(a, b, k => k)
  
}