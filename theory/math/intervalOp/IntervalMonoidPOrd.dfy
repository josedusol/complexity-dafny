include "../abstractAlgebra/MonoidPOrd.dfy"

/******************************************************************************
  Fold operator over a finite integer interval assuming codomain
  is equipt with a partially ordered monoid
******************************************************************************/

abstract module IntervalMonoidPOrd refines MonoidPOrd {

  // ⊗_{k=a}^{b}f(k)
  opaque ghost function bigOp(a:int, b:int, f:int-->T): T
    requires forall k :: a <= k <= b ==> f.requires(k)
    decreases b - a
  {
    if a > b then id
             else op(f(a), bigOp(a+1, b, f))
  }

  lemma lem_bigOpDef(a:int, b:int, f:int->T)
    ensures a >  b ==> bigOp(a, b, f) == id
    ensures a <= b ==> bigOp(a, b, f) == op(f(a), bigOp(a+1, b, f))
  { 
    reveal bigOp();
  }

  // a > b ⟹ ⊗_{k=a}^{b}f(k) = id
  lemma lem_BaseCase(a:int, b:int, f:int->T)
    ensures a > b ==> bigOp(a, b, f) == id
  { 
    lem_bigOpDef(a, b, f);
  }

  // a <= b ⟹ ⊗_{k=a}^{b}f(k) = f(a) ⊗ ⊗_{k=a+1}^{b}f(k)
  lemma lem_SplitFirst(a:int, b:int, f:int->T)
    requires a <= b
    ensures  bigOp(a, b, f) == op(f(a), bigOp(a+1, b, f))
  { 
    lem_bigOpDef(a, b, f);
  }

  // a == b ⟹ ⊗_{k=a}^{b}f(k) = f(a)
  lemma lem_SplitUnit(a:int, b:int, f:int->T)
    requires a == b
    ensures  bigOp(a, b, f) == f(a)
  { 
    calc {
         bigOp(a, a, f);
      == { lem_SplitFirst(a, a, f); }
         op(f(a), bigOp(a+1, a, f));
      == { lem_bigOpDef(a+1, a, f); }
         op(f(a), id);
      == { lem_IdentityAuto(); }
         f(a);
    }
  }

  // a <= b ⟹ ⊗_{k=a}^{b}f(k) = ⊗_{k=a}^{b-1}f(k) ⊗ f(b)
  lemma {:induction false} lem_SplitLast(a:int, b:int, f:int->T)
    requires a <= b
    ensures  bigOp(a, b, f) == op(bigOp(a, b-1, f), f(b))
    decreases b - a
  { 
    if a == b {   
      // BC: a > b
      calc {
           bigOp(b, b, f);
        == { lem_bigOpDef(b, b, f); }
           op(f(b), bigOp(b+1, b, f));
        == { lem_bigOpDef(b+1, b, f); }
           op(f(b), id);
        == { lem_IdentityAuto();  }
           op(id, f(b)) ;
        == { lem_bigOpDef(b, b-1, f); }
           op(bigOp(b, b-1, f), f(b));       
      }
    } else {  
      // Step. a <= b
      //   IH: ⊗(a+1, b, f) = ⊗(a+1, b-1, f) ⊗ f(b)
      //    T: ⊗(a, b, f)   = ⊗(a, b-1, f)   ⊗ f(b)
      calc {  
           bigOp(a, b, f);
        == { lem_SplitFirst(a, b, f); } 
           op(f(a), bigOp(a+1, b, f));
        == { lem_SplitLast(a+1, b, f); }  // by IH
           op(f(a), (op(bigOp(a+1, b-1, f), f(b))));
        == { lem_AssociativeAuto(); }
           op(op(f(a), bigOp(a+1, b-1, f)), f(b));
        == { lem_SplitFirst(a, b-1, f); }
           op(bigOp(a, b-1, f), f(b));           
      }
    }
  }

  lemma lem_SplitLastAuto(a:int, b:int)
    requires a <= b
    ensures  forall f:int->T :: bigOp(a, b, f) == op(bigOp(a, b-1, f), f(b))
  { 
    forall f:int->T
      ensures bigOp(a, b, f) == op(bigOp(a, b-1, f), f(b))
    {
      lem_SplitLast(a, b, f);
    }
  }

  // a <= b+1 ⟹ ⊗_{k=a}^{b}f(k) = ⊗_{k=a+d}^{b+d}f(k-d)
  lemma {:induction false} lem_ShiftIndex(a:int, b:int, d:int, f:int->T)
    requires a <= b+1
    ensures  bigOp(a, b, f) == bigOp(a+d, b+d, k => f(k-d))
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           bigOp(b+1, b, f);
        == { lem_bigOpDef(b+1, b, f); }
           id;
        == { lem_bigOpDef(b+1+d, b+d, k => f(k-d)); }
           bigOp(b+1+d, b+d, k => f(k-d));       
      }
    } else {  
      // Step. a <= b
      //   IH: ⊗(a+1, b, f) = ⊗((a+d)+1, b+d, k => f(k-d))
      //    T: ⊗(a, b, f)   = ⊗(a+d, b+d, k => f(k-d))
      calc {  
           bigOp(a, b, f);
        == { lem_SplitFirst(a, b, f); } 
           op(f(a), bigOp(a+1, b, f));
        == { lem_ShiftIndex(a+1, b, d, f); }  // by IH
           op(f(a), bigOp(a+1+d, b+d, k => f(k-d)));
        == op((k => f(k-d))(a+d), bigOp((a+d)+1, b+d, k => f(k-d)));
        == { lem_SplitFirst(a+d, b+d, k => f(k-d)); }
           bigOp(a+d, b+d, k => f(k-d));           
      }
    }
  } 

  // a <= j <= b ⟹ ⊗_{k=a}^{b}f = ⊗_{k=a}^{j}f + ⊗_{k=j+1}^{b}f
  lemma {:induction false} lem_Split(a:int, b:int, j:int, f:int->T)
    requires a <= j <= b
    ensures bigOp(a, b, f) == op(bigOp(a, j, f), bigOp(j+1, b, f))
    decreases b - a
  {
    if a == b+1 {
      // BC: a > b 
      assert true;  // trivial
    } else {  
      // Step. a <= b
      //   IH: ⊗(a+1, b, f) = ⊗(a+1, j, f) ⊗ ⊗(j+1, b, f)
      //    T: ⊗(a, b, f)   = ⊗(a, j, f) ⊗ ⊗(j+1, b, f)
      if a == j {
        calc {  
             bigOp(j, b, f);
          == { lem_SplitFirst(j, b, f); } 
             op(f(j), bigOp(j+1, b, f));
          == { lem_SplitUnit(j, j, f); } 
             op(bigOp(j, j, f), bigOp(j+1, b, f));   
        }
      } else if a < j {
        calc {  
             bigOp(a, b, f);
          == { lem_SplitFirst(a, b, f); } 
             op(f(a), bigOp(a+1, b, f));
          == { lem_Split(a+1, b, j, f); }  // by IH
             op(f(a), op(bigOp(a+1, j, f), bigOp(j+1, b, f)));
          == { lem_AssociativeAuto(); }
             op(op(f(a), bigOp(a+1, j, f)), bigOp(j+1, b, f));
          == { lem_SplitFirst(a, j, f); } 
             op(bigOp(a, j, f), bigOp(j+1, b, f));        
        }
      }
    }
  } 

  // a <= j <= b ⟹ ⊗_{k=a}^{b}f = ⊗_{k=a}^{j-1}f ⊗ ⊗_{k=j}^{b}f
  lemma lem_Split2(a:int, b:int, j:int, f:int->T)
    requires a <= j <= b
    ensures bigOp(a, b, f) == op(bigOp(a, j-1, f), bigOp(j, b, f))
    decreases b - a
  {
    calc {
         bigOp(a, b, f);
      == { lem_Split(a, b, j, f); }
         op(bigOp(a, j, f), bigOp(j+1, b, f)); 
      == { lem_SplitLast(a, j, f); }
         op(op(bigOp(a, j-1, f), f(j)), bigOp(j+1, b, f)); 
      == { lem_AssociativeAuto(); }
         op(bigOp(a, j-1, f), op(f(j), bigOp(j+1, b, f)));      
      == { lem_SplitFirst(j, b, f); }
         op(bigOp(a, j-1, f), bigOp(j, b, f));
    }
  }

  // a <= b+1 ⟹ ⊗_{k=a}^{b}(f(k)⊗g(k)) = ⊗_{k=a}^{b}f ⊗ ⊗_{k=a}^{b}g
  lemma {:induction false} lem_LinearityAdditive(a:int, b:int, f:int->T, g:int->T)
    requires a <= b+1
    ensures  bigOp(a, b, k => op(f(k), g(k))) == op(bigOp(a, b, f), bigOp(a, b, g))
    // TODO

  // a <= b+1 ∧  (∀ k : a<=k<=b : f(k) == g(k)) 
  //          ⟹ ⊗_{k=a}^{b}f = ⊗_{k=a}^{b}g
  lemma {:induction false} lem_Leibniz(a:int, b:int, f:int->T, g:int->T)
    requires a <= b+1
    requires H: forall k:int :: a <= k <= b ==> f(k) == g(k)
    ensures  bigOp(a, b, f) == bigOp(a, b, g)
    decreases b - a
  {
    if a == b+1 {   
      // BC: a > b
      calc {
           bigOp(b+1, b, f);
        == { lem_BaseCase(b+1, b, f); }
           id;
        == { lem_BaseCase(b+1, b, g); }
           bigOp(b+1, b, g);       
      }
    } else {  
      // Step. a <= b
      //   IH: ⊗(a+1, b, f) = ⊗(a+1, b, g)
      //    T: ⊗(a, b, f)   = ⊗(a, b, g)
      calc {  
           bigOp(a, b, f);
        == { lem_SplitFirst(a, b, f); } 
           op(f(a), bigOp(a+1, b, f));
        == { reveal H; assert f(a) == g(a); }
           op(g(a), bigOp(a+1, b, f));
        == { reveal H; lem_Leibniz(a+1, b, f, g); }  // by IH
           op(g(a), bigOp(a+1, b, g));
        == { lem_SplitFirst(a, b, g); }
           bigOp(a, b, g);           
      }
    }
  } 
  
  // // Pointwise strict inequalities can be lifted to strict inequality of folded result
  // // a <= b ∧  (∀ k : a<=k<=b : f(k) < g(k)) 
  // //        ⟹ ⊗_{k=a}^{b}f < ⊗_{k=a}^{b}g
  // lemma {:induction false} lem_StrictIncr(a:int, b:int, f:int->T, g:int->T)
  //   requires a <= b
  //   requires H: forall k:int :: a <= k <= b ==> Ord.Lt(f(k), g(k))
  //   ensures  Ord.Lt(bigOp(a, b, f), bigOp(a, b, g))
  //   decreases b - a
  // {
  //   if a == b { 
  //     // BC: a = b  
  //     assert bigOp(a, a, f) == f(a)
  //       by { lem_SplitUnit(a, a, f); }
  //     assert Ord.Lt(f(a), g(a)) 
  //       by { reveal H; } 
  //     assert g(a) == bigOp(a, a, g)
  //       by { lem_SplitUnit(a, a, g); }

  //     // The clean calculational style would be as follows:  
  //     // calc {
  //     //      sum(a, a, f);
  //     //   == { ISR.lem_SplitUnit(a, a, f); reveal sum(); }
  //     //      f(a);
  //     //   <  { reveal H; assert f(a) < g(a); }
  //     //      g(a);   
  //     //   == { ISR.lem_SplitUnit(a, a, g); reveal sum(); }
  //     //      sum(a, a, g);       
  //     // }        
  //   } else {  
  //     // Step. a < b
  //     //   IH: ⊗(a+1, b, f) < ⊗(a+1, b, g)
  //     //    T: ⊗(a, b, f)   < ⊗(a, b, g)
  //     assert A: bigOp(a, b, f) == op(f(a), bigOp(a+1, b, f))
  //       by { lem_SplitFirst(a, b, f); } 
  //     assert B: Ord.Lt(op(f(a), bigOp(a+1, b, f)), op(g(a), bigOp(a+1, b, f)))
  //       by { reveal H; lem_Lt_WeakMonoAuto(); }
  //     assert C: Ord.Lt(op(g(a), bigOp(a+1, b, f)), op(g(a), bigOp(a+1, b, g)))
  //       by { reveal H; lem_StrictIncr(a+1, b, f, g); lem_Lt_WeakMonoAuto(); }  // IH
  //     assert D: op(g(a), bigOp(a+1, b, g)) == bigOp(a, b, g)
  //       by { lem_SplitFirst(a, b, g); }  
  //     // Now apply laws transitivity of Ord.Lt
  //     assert Ord.Lt(bigOp(a, b, f), bigOp(a, b, g))
  //       by { reveal A, B, C, D; Ord.lem_Lt_TransAuto(); }

  //     // The clean calculational style would be as follows:
  //     // calc {  
  //     //      sum(a, b, f);
  //     //   == { ISR.lem_SplitFirst(a, b, f); } 
  //     //      f(a) + sum(a+1, b, f);
  //     //   <  { reveal H; assert f(a) < g(a); }
  //     //      g(a) + sum(a+1, b, f);
  //     //   <  { lem_StrictIncr(a+1, b, f, g); }  // by IH
  //     //      g(a) + sum(a+1, b, g);
  //     //   == { ISR.lem_SplitFirst(a, b, g); }
  //     //      sum(a, b, g);           
  //     // }
  //   }
  // }     
 
  // Pointwise inequalities can be lifted to inequality of folded result
  // a <= b+1 ∧  (∀ k : a<=k<=b : f(k) <= g(k)) 
  //          ⟹ ⊗_{k=a}^{b}f <= ⊗_{k=a}^{b}g
  lemma {:induction false} lem_MonoIncr(a:int, b:int, f:int->T, g:int->T)
    requires a <= b+1
    requires H: forall k:int :: a <= k <= b ==> Ord.Leq(f(k), g(k))
    ensures  Ord.Leq(bigOp(a, b, f), bigOp(a, b, g))
    decreases b - a
  {
    if a == b+1 { 
      // BC: a > b  
      assert bigOp(b+1, b, f) == id
        by { lem_BaseCase(b+1, b, f); }
      assert bigOp(b+1, b, g) == id
        by { lem_BaseCase(b+1, b, g); }
      Ord.lem_Leq_SubstEqAuto();
 
      // The clean calculational style would be as follows:  
      // calc {
      //      sum(b+1, b, f);
      //   == { ISR.lem_BaseCase(b+1, b, f); }
      //      0.0;
      //   == { ISR.lem_BaseCase(b+1, b, g); }
      //      sum(b+1, b, g);       
      // }    
    } else {  
      // Step. a <= b
      //   IH: ⊗(a+1, b, f) <= ⊗(a+1, b, g)
      //    T: ⊗(a, b, f)   <= ⊗(a, b, g)
      assert A: bigOp(a, b, f) == op(f(a), bigOp(a+1, b, f))
        by { lem_SplitFirst(a, b, f); } 
      assert B: Ord.Leq(op(f(a), bigOp(a+1, b, f)), op(g(a), bigOp(a+1, b, f)))
        by { reveal H; lem_Leq_MonoAuto(); }
      assert C: Ord.Leq(op(g(a), bigOp(a+1, b, f)), op(g(a), bigOp(a+1, b, g)))
        by { reveal H; lem_MonoIncr(a+1, b, f, g); lem_Leq_MonoAuto(); }  // IH
      assert D: op(g(a), bigOp(a+1, b, g)) == bigOp(a, b, g)
        by { lem_SplitFirst(a, b, g); }  
      // Now apply laws transitivity of Ord.Lt
      assert Ord.Leq(bigOp(a, b, f), bigOp(a, b, g))
        by { reveal A, B, C, D; Ord.lem_Leq_TransAuto(); } 

      // The clean calculational style would be as follows:
      // calc {  
      //      sum(a, b, f);
      //   == { ISR.lem_SplitFirst(a, b, f); } 
      //      f(a) + sum(a+1, b, f);
      //   <= { assert f(a) <= g(a);  }
      //      g(a) + sum(a+1, b, f);
      //   <= { lem_MonoIncr(a+1, b, f, g); }  // by IH
      //      g(a) + sum(a+1, b, g);
      //   == { ISR.lem_SplitFirst(a, b, g); }
      //      sum(a, b, g);           
      // }
    }
  }     

  /******************************************************************************
    Universal closures
  ******************************************************************************/

}