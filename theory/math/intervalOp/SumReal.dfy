include "../Function.dfy"
include "../LemFunction.dfy"
include "./IntervalSumReal.dfy"

/******************************************************************************
  Sum over integer intervals and real codomain
******************************************************************************/

module SumReal {

  import opened Function  
  import opened LemFunction 
  import ISR = IntervalSumReal

  // Σ_{k=a}^{b}f(k) = ⊗_{k=a}^{b}f(k)
  ghost function sum(a:int, b:int, f:int-->real): real
    requires forall k :: a <= k <= b ==> f.requires(k)
  {
    ISR.bigOp(a, b, f)
  } 

  // a <= b ∧ (∀ k : a<=k<=b : f(k) > 0) ⟹ Σ_{k=a}^{b}f(k) > 0
  lemma {:induction false} lem_Positive(a:int, b:int, f:int->real)
    requires a <= b
    requires forall k :: a <= k <= b ==> f(k) > 0.0
    ensures  sum(a, b, f) > 0.0
    decreases b - a
  { 
    if a == b {   
      // BC: a = b
      calc {
           sum(b, b, f);
        == { ISR.lem_SplitUnit(b, b, f); reveal sum(); }
           f(b);
        >  0.0;
      }
    } else {
      // Step. a < b
      //   IH: Σ(a+1, b, f) > 0
      //    T: Σ(a, b, f)   > 0
      calc {  
           sum(a, b, f);
        == { ISR.lem_SplitFirst(a, b, f); } 
           f(a) + sum(a+1, b, f);
        >  0.0 + sum(a+1, b, f);
        > { lem_Positive(a+1, b, f); }  // by IH
           0.0 + 0.0;
        == 0.0;           
      }
    }    
  }

  // (∀ k : a<=k<=b : f(k) >= 0) ⟹ Σ_{k=a}^{b}f(k) >= 0
  lemma {:induction false} lem_NonNegative(a:int, b:int, f:int->real)
    requires a <= b+1
    requires forall k :: a <= k <= b ==> f(k) >= 0.0
    ensures  sum(a, b, f) >= 0.0
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a = b+1
      calc {
           sum(b+1, b, f);
        == { ISR.lem_BaseCase(b+1, b, f); }
           0.0;
      }
    } else {
      // Step. a <= b
      //   IH: Σ(a+1, b, f) >= 0
      //    T: Σ(a, b, f)   >= 0
      calc {  
           sum(a, b, f);
        == { ISR.lem_SplitFirst(a, b, f); } 
           f(a) + sum(a+1, b, f);
        >= 0.0 + sum(a+1, b, f);
        >= { lem_NonNegative(a+1, b, f); }  // by IH
           0.0 + 0.0;
        == 0.0;           
      }
    }    
  }

  // i <= j+1 ⟹ c*Σ_{k=i}^{j}f(k) = Σ_{k=i}^{j}c*f(k)
  lemma {:induction false} lem_LinearityConst(a:int, b:int, c:real, f:int->real)
    requires a <= b+1
    ensures  c*sum(a, b, f) == sum(a, b, k => c*f(k))
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           c*sum(b+1, b, f);
        == { ISR.lem_BaseCase(b+1, b, f); }
           0.0;
        == { ISR.lem_BaseCase(b+1, b, k => c*f(k)); }
           sum(b+1, b, k => c*f(k));       
      }
    } else {  
      // Step. a <= b
      //   IH: c*Σ(a+1, b, f) = c*Σ(a+1, b, k => c*f(k))
      //    T: c*Σ(a, b, f)   = c*Σ(a, b, k => f(k))
      calc {  
           c*sum(a, b, f);
        == { ISR.lem_SplitFirst(a, b, f); } 
           c*(f(a) + sum(a+1, b, f));
        == c*f(a) + c*sum(a+1, b, f);         
        == { lem_LinearityConst(a+1, b, c, f); }  // by IH
           c*f(a) + sum(a+1, b, k => c*f(k)); 
        == (k => c*f(k))(a) + sum(a+1, b, k => c*f(k));
        == { ISR.lem_SplitFirst(a, b, k => c*f(k)); } 
           sum(a, b, k => c*f(k));           
      } 
    }  
  }

  // a <= b+1 ⟹ Σ_{k=a}^{b}c = c*(b - a + 1)
  lemma {:induction false} lem_Const(a:int, b:int, c:real)
    requires a <= b+1
    ensures  sum(a, b, k => c) == c * (b - a + 1) as real
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           sum(b+1, b, k => c); 
        == { ISR.lem_BaseCase(b+1, b, k => c); } 
           0.0; 
        == (b - (b+1) + 1) as real;
      }
    } else {  
      // Step. a <= b
      //   IH: Σ(a+1, b, k => c) = c*(b - (a+1) + 1) = c*(b - a)
      //    T: Σ(a, b, k => c)   = c*(b - a + 1) 
      calc {  
           sum(a, b, k => c);
        == { ISR.lem_SplitFirst(a, b, k => c); }
           c + sum(a+1, b, k => c);
        == { lem_Const(a+1, b, c); }  // by IH
           (c + c* (b - (a+1) + 1) as real);
        == c + c*((b - a) as real);      
        == c* (b - a + 1) as real;             
      }
    }
  }

  lemma lem_ConstAuto(a:int, b:int)
    requires a <= b+1
    ensures  forall c:real :: sum(a, b, k => c) == c * (b - a + 1) as real
  { 
    forall c:real
      ensures sum(a, b, k => c) == c * (b - a + 1) as real
    {
      lem_Const(a, b, c);
    }
  } 

  // a <= b+1 ⟹ Σ_{k=a}^{b}k = (b*(b+1) + a*(1-a))/2 
  lemma {:induction false} lem_Interval(a:int, b:int)
    requires a <= b+1 
    decreases b - a
    ensures sum(a, b, k => k as real) == (b*(b+1) + a*(1-a)) as real / 2.0
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           sum(b+1, b, k => k as real);
        == { ISR.lem_BaseCase(b+1, b, k => k as real); }
           0.0;
        == (b*(b+1) + ((b+1))*(1-((b+1)))) as real / 2.0;
      }
    } else {  
      // Step. a <= b
      //   IH: Σ(a+1, b, K => k) = (b*(b+1) + (a+1)*(1-(a+1)))/2 
      //    T: Σ(a, b, k => k)   = (b*(b+1) + a*(1-a))/2 
      calc {  
           sum(a, b, k => k as real);
        == { ISR.lem_SplitFirst(a, b, k => k as real); }
           a as real + sum(a+1, b, k => k as real);
        == { lem_Interval(a+1, b); }  // by IH
           a as real + (b*(b+1) + (a+1)*(1-(a+1))) as real / 2.0;
        == (b*(b+1) + a*(1-a)) as real / 2.0;            
      }
    } 
  }

  // Pointwise strict inequalities can be lifted to strict inequality of folded result
  // a <= b ∧  (∀ k : a<=k<=b : f(k) < g(k)) 
  //        ⟹ Σ_{k=a}^{b}f < Σ_{k=a}^{b}g
  lemma {:induction false} lem_StrictIncr(a:int, b:int, f:int->real, g:int->real)
    requires a <= b
    requires forall k:int :: a<=k<=b ==> f(k) < g(k)
    ensures sum(a, b, f) < sum(a, b, g)
    decreases b - a
  {
    if a == b {   
      // BC: a = b
      calc {
           sum(a, a, f);
        == { ISR.lem_SplitUnit(a, a, f); }
           f(a);
        <  { assert f(a) < g(a); }
           g(a);    
        == { ISR.lem_SplitUnit(a, a, g); }
           sum(a, a, g);       
      }
    } else {  
      // Step. a < b
      //   IH: Σ(a+1, b, f) < Σ(a+1, b, g)
      //    T: Σ(a, b, f)   < Σ(a, b, g)
      calc {  
           sum(a, b, f);
        == { ISR.lem_SplitFirst(a, b, f); } 
           f(a) + sum(a+1, b, f);
        < { assert f(a) < g(a); }
           g(a) + sum(a+1, b, f);
        < { lem_StrictIncr(a+1, b, f, g); }  // by IH
           g(a) + sum(a+1, b, g);
        == { ISR.lem_SplitFirst(a, b, g); }
           sum(a, b, g);           
      }
    }
  } 


}