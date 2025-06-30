
include "./math/ExpReal.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemBoundsNat.dfy"
include "./math/LemFunction.dfy"
include "./math/MaxMin.dfy"
include "./math/SumReal.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityR0.dfy"

module MasterLR {  
  import opened ExpReal 
  import opened FloorCeil   
  import opened LemBoundsNat
  import opened LemFunction
  import opened MaxMin
  import opened SumReal
  import opened TypeR0 
  import opened ComplexityR0

  // Following recurrence models a recursive computation where
  //      a = Branching factor, or number of recursive calls. Controls the breadth of computation.
  //      b = Base case condition.
  //      s = Step Size. Controls the depth of computation.
  //      c = Cost at the base case
  //   w(n) = Additive term, cost by recursive call.
  //
  //  It is assumed sub-exponential work is done at each recursive call
  //  (if not we would be doing exponential work from the very beggining!).
  //
  // Let T:nat->R0 be such that
  //   T(n) = / c                 , n <= b        
  //          \ a*T(n-s) + w(n)   , n > b           
  // where a>0, s>0, b >= s-1 and w in O(n^k) for some k.    
  // Then:
  //   T(n) = / O(n^{k+1})        , a = 1
  //          \ O(n^k*a^{n/s})    , a > 1
  //
  // Note. Always match w to the tightest Θ(n^k) it belongs. 
  //       - It is neccesary and sufficient to conclude the 
  //         thight Θ(n^{k+1}) bound when a=1.
  //       - It is neccesary, but not always sufficient, to conclude the 
  //         thight Θ(n^k*a^{n/s}) bound when a>1.
  //       In general, we can only be sure of O type bounds. Thigher Θ bounds
  //       require a case by case analysis.
  lemma thm_masterMethodLR(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, k:R0)
    requires a > 0 && s > 0 && b >= s-1
    requires bigO(w, n => pow(n as R0, k)) 
    requires forall n:nat :: T(n) == TbodyLR(a, b, c, s, T, w, n) 

    ensures a == 1 ==> bigO(T, (n:nat) => pow(n as R0, k + 1.0))
    ensures a > 1  ==> bigO(T, (n:nat) => pow(n as R0, k)*pow(a as R0, (n/s) as R0))
  {
    // 1. Prove: ∀ n : T(n) = a^m*c + S(n) where m=ceil((n-b)/s)
    assert forall n:nat :: T(n) == TsumForm(a, b, c, s, w, n)
      by { lem_mmLR_sumForm(a, b, c, s, T, w); }

    // 2. Prove: ∃ d: ∀ n : S(n) <= d*n^k*sum_{i=0}^{m-1}a^i
    assert exists d :: SupBoundPred(a, b, s, w, k, d)
      by { lem_mmLR_SupBound(a, b, c, s, T, w, k); }

    // Cases on a:
    if a == 1 {    
  //     assert sumr(0, m-1, i => powr(a as R0, i as real)) == m;
  //     assert bigOR0(n => m, n => powr(n as R0, 1.0));
  //
  //     assert bigOR0(T, (n:nat) => powr(n as R0, k + 1.0));
    } else if a > 1 {
  //     assert sumr(0, m-1, i => powr(a as R0, i as real)) == ...;
  //     assert bigOR0(n => ..., n => powr(a as R0, (n/s) as R0));
  //      
  //     assert bigOR0(T, (n:nat) => powr(n as R0, k)*powr(a as R0, (n/s) as R0));
    }
    // TODO
    assert false;
  }

  opaque ghost function TbodyLR(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, n:nat) : R0
    requires b >= s-1
  {    
    if   n <= b 
    then c
    else (a as R0)*T(n - s) + w(n)    
  } 

  // Expression: ceil((n-b)/s)
  opaque ghost function m(b:nat, s:nat, n:nat) : int
    requires s > 0
  {    
    max(0, ceil(((n-b) as real)/(s as real)))  
  } 

  // Expression: a^m*c + S(n)
  opaque ghost function TsumForm(a:nat, b:nat, c:R0, s:nat, w:nat->R0, n:nat) : real
    requires s > 0
  {    
    pow(a as R0, m(b,s,n) as real)*c + S(a, b, s, w, n)    
  } 

  // Expression: sum_{i=0}^{m-1}a^i*w(n-i*s)
  opaque ghost function S(a:nat, b:nat, s:nat, w:nat->R0, n:nat) : real
    requires s > 0
  {    
    sum(0, m(b,s,n)-1, i => S1(a,i)*S2(s,w,n,i))      
  } 

  // Expression: a^i
  opaque ghost function S1(a:nat, i:int) : real
  {    
    pow(a as R0, i as real)     
  } 

  // Expression: n-i*s
  opaque ghost function S2(s:nat, w:nat->R0, n:nat, i:int) : real
  {    
    liftD(w,0.0)(n-i*s)
  } 

  // Expression: d*n^k*sum_{i=0}^{m-1}a^i
  opaque ghost function SupBound(a:nat, b:nat, s:nat, w:nat->R0, k:R0, n:nat, d:R0) : real
    requires s > 0
  {    
    d*pow(n as R0, k)*sum(0, m(b,s,n)-1, i => S1(a,i))    
  } 

  // Predicate: ∀ n : S(n) <= SupBound(n,d)
  ghost predicate SupBoundPred(a:nat, b:nat, s:nat, w:nat->R0, k:R0, d:R0)
    requires s > 0
  {    
    forall n:nat :: S(a, b, s, w, n) <= SupBound(a, b, s, w, k, n, d) 
  } 

  // If n <= b then m = 0
  // If n > b  then m = ceil((n-b)/s)
  lemma lem_mmLR_mValue(b:nat, s:nat, n:nat)  
    requires s > 0 && b >= s-1
    ensures  n <= b ==> m(b,s,n) == 0
    ensures  n >  b ==> m(b,s,n) == ceil(((n-b) as real)/(s as real))
                        && m(b,s,n) >= 1
  {
    if n <= b {
      calc {  // ceil((n-b)/s) <= 0
           ceil(((n-b) as real)/(s as real));
        <= { assert ((n-b) as real)/(s as real) <= 0.0; 
           lem_ceilxLEQnIFFxLEQn(((n-b) as real)/(s as real),0); }
           0;
      }  
      calc {
           m(b,s,n);
        == { reveal m(); }
           max(0, ceil(((n-b) as real)/(s as real)));
        == max(0, 0);
        == 0;
      }  
    } else if n > b {
      calc {  // ceil((n-b)/s) > 0
          ceil(((n-b) as real)/(s as real));
        > { assert ((n-b) as real)/(s as real) > 0.0; 
            lem_ceilxLEQnIFFxLEQn(((n-b) as real)/(s as real),0); }
          0;
      }  
      calc {
           m(b,s,n);
        == { reveal m(); }
           max(0, ceil(((n-b) as real)/(s as real)));
        == ceil(((n-b) as real)/(s as real));
      }  
    }
  }

  // ∀ n : T(n) = a^m*c + sum_{i=0}^{m-1}a^i*w(n-i*s) where m=ceil((n-b)/s)
  lemma lem_mmLR_sumForm(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0)  
    requires a > 0 && s > 0 && b >= s-1
    requires forall n:nat :: T(n) == TbodyLR(a, b, c, s, T, w, n) 
    ensures  forall n:nat :: T(n) == TsumForm(a, b, c, s, w, n)     
  {
    forall n:nat
      ensures T(n) == TsumForm(a, b, c, s, w, n)
    {
      lem_mmLR_sumFormInd(a, b, c, s, T, w, n);
    }
  }

  lemma lem_mmLR_sumFormInd(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, n:nat)  
    requires a > 0 && s > 0 && b >= s-1
    requires forall n:nat :: T(n) == TbodyLR(a, b, c, s, T, w, n)  
    ensures  T(n) == TsumForm(a, b, c, s, w, n)    
  {
    var mv := m(b,s,n);
    var aR := a as R0; 
    if n <= b {
      // CB. n <= b
      calc {
           T(n);
        == { reveal TbodyLR(); }
           c;
        == { lem_mmLR_mValue(b, s, n); reveal S, sum();  }
           c + S(a, b, s, w, n);
        == { lem_mmLR_mValue(b, s, n); lem_powZero(aR); }
           pow(aR, mv as real)*c + S(a, b, s, w, n);
        == { reveal TsumForm(); } 
           TsumForm(a, b, c, s, w, n);  
      }      
    } else {
      // Step. n > b
      //   IH: T(n-s) = TsumForm(a, b, c, s, w, n-s)   
      //    T: T(n)   = TsumForm(a, b, c, s, w, n)   
      var mv' := m(b,s,n-s);
      assert mv >= 1 by { lem_mmLR_mValue(b, s, n); }

      // First, we prove various named rewritings that will be used in the final proof
      assert mRewr: mv' == mv - 1 
        by { lem_mmLR_mRewr(a,b,s,n); }
      assert sumRewr:    S(a, b, s, w, n-s) 
                      == sum(0, mv-2, i => S1(a,i)*S2(s,w,n,i+1))
        by { lem_mmLR_sumRewr(a, b, c, s, T, w, n); }
      assert sumRewr2:   aR*sum(0, mv-2, i => S1(a,i)*S2(s,w,n,i+1))
                      == sum(0, mv-2, i => S1(a,i+1)*S2(s,w,n,i+1))
        by { lem_mmLR_sumRewr2(a, b, c, s, T, w, n); }  
      assert sumRewr3:   sum(0, mv-2, i => S1(a,i+1)*S2(s,w,n,i+1))  
                      == sum(1, mv-1, i => S1(a,i)*S2(s,w,n,i))
        by { lem_mmLR_sumRewr3(a, b, c, s, T, w, n); }
      assert wRewr: w(n) == S1(a,0)*S2(s,w,n,0)
        by {
          calc {
               S1(a,0)*S2(s,w,n,0);
            == { reveal S2(); } 
               S1(a,0)*liftD(w,0.0)(n-0*s);
            == { reveal S1(); } 
               pow(a as R0, 0 as real)*liftD(w,0.0)(n-0*s); 
            == { lem_powZero(a as R0); }    
               1.0*liftD(w,0.0)(n-0*s); 
            == { lem_powZero(a as R0); }    
               liftD(w,0.0)(n);             
          }      
        }  

      // Finally, we prove the desired goal
      calc {
           T(n);
        == { reveal TbodyLR(); assert n > b; }
           aR*T(n - s) + w(n); 
        == { lem_mmLR_sumFormInd(a, b, c, s, T, w, n-s); }
           aR*TsumForm(a, b, c, s, w, n-s) + w(n); 
        == { reveal TsumForm(); }
           aR*(pow(aR, mv' as real)*c + S(a, b, s, w, n-s)) + w(n);  
        == { reveal mRewr; }
           aR*(pow(aR, (mv-1) as real)*c + S(a, b, s, w, n-s)) + w(n); 
        == aR*pow(aR, (mv-1) as real)*c + aR*S(a, b, s, w, n-s) + w(n); 
        == { lem_powDef(aR, (mv-1) as real); }
           pow(aR, mv as real)*c + aR*S(a, b, s, w, n-s) + w(n);     
        == { reveal sumRewr; }
           pow(aR, mv as real)*c + aR*sum(0, mv-2, i => S1(a,i)*S2(s,w,n,i+1)) + w(n);
        == { reveal sumRewr2; }
           pow(aR, mv as real)*c + sum(0, mv-2, i => S1(a,i+1)*S2(s,w,n,i+1)) + w(n);    
        == { reveal sumRewr3; }
           pow(aR, mv as real)*c + sum(1, mv-1, i => S1(a,i)*S2(s,w,n,i)) + w(n); 
        == { reveal wRewr; }
           pow(aR, mv as real)*c + sum(1, mv-1, i => S1(a,i)*S2(s,w,n,i)) + S1(a,0)*S2(s,w,n,0); 
        == { reveal sum(); }
           pow(aR, mv as real)*c + sum(0, mv-1, i => S1(a,i)*S2(s,w,n,i));           
        == { reveal TsumForm(), S(); }
           TsumForm(a, b, c, s, w, n);                                                                   
      }  
    } 
  }

  lemma lem_mmLR_sumRewr3(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, n:nat)  
    requires a > 0 && s > 0 && b >= s-1
    requires n > b
    requires m(b,s,n) >= 1
    ensures    sum(0, m(b,s,n)-2, i => S1(a,i+1)*S2(s,w,n,i+1))  
            == sum(1, m(b,s,n)-1, i => S1(a,i)*S2(s,w,n,i))
  {
    var mv := m(b,s,n); assert mv >= 1;
    calc {
         sum(0, mv-2, i => S1(a,i+1)*S2(s,w,n,i+1));
      == { lem_sum_shiftIndex(0, mv-2, 1, i => S1(a,i+1)*S2(s,w,n,i+1)); } 
         sum(1, mv-1, l => (i => S1(a,i+1)*S2(s,w,n,i+1))(l-1)); 
      == { reveal S2();
           assert forall l :: 1 <= l <= mv-1 ==> 
             (i => S1(a,i+1)*S2(s,w,n,i+1))(l-1) == S1(a,l)*S2(s,w,n,l);
           lem_sum_leibniz(1, mv-1, l => (i => S1(a,i+1)*S2(s,w,n,i+1))(l-1), 
                                    l => S1(a,l)*S2(s,w,n,l)); } 
         sum(1, mv-1, i => S1(a,i)*S2(s,w,n,i));            
    }      
  }

  lemma {:isolate_assertions} lem_mmLR_sumRewr2(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, n:nat)  
    requires a > 0 && s > 0 && b >= s-1
    requires n > b
    requires m(b,s,n) >= 1
    ensures    (a as R0)*sum(0, m(b,s,n)-2, i => S1(a,i)*S2(s,w,n,i+1))
            == sum(0, m(b,s,n)-2, i => S1(a,i+1)*S2(s,w,n,i+1))
  {
    var mv := m(b,s,n); assert mv >= 1;
    var aR := a as R0;
      calc {
           aR*sum(0, mv-2, i => S1(a,i)*S2(s,w,n,i+1));
        == { lem_sum_linearityConst(0, mv-2, aR, i => S1(a,i)*S2(s,w,n,i+1)); }
           sum(0, mv-2, l => aR*(i => S1(a,i)*S2(s,w,n,i+1))(l)); 
        == { reveal S1(); assert aR == a as real;
             assert forall l :: 0 <= l <= mv-2 ==> 
               aR*(i => S1(a,i)*S2(s,w,n,i+1))(l) == aR*pow(a as real,l as real)*S2(s,w,n,l+1);
             lem_sum_leibniz(0, mv-2, l => aR*(i => S1(a,i)*S2(s,w,n,i+1))(l), 
                                      l => aR*pow(a as real,l as real)*S2(s,w,n,l+1)); } 
           sum(0, mv-2, i => aR*pow(aR,i as real)*S2(s,w,n,i+1));  
        == { reveal S1(); lem_powDefAll();
             assert forall l :: 0 <= l <= mv-2 ==> 
               aR*pow(aR,l as real)*S2(s,w,n,l+1) == S1(a,l+1)*S2(s,w,n,l+1);
             lem_sum_leibniz(0, mv-2, i => aR*pow(aR,i as real)*S2(s,w,n,i+1), 
                                       i => S1(a,i+1)*S2(s,w,n,i+1)); }       
           sum(0, mv-2, i => S1(a,i+1)*S2(s,w,n,i+1));       
      }         
  }

  lemma lem_mmLR_sumRewr(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, n:nat)  
    requires a > 0 && s > 0 && b >= s-1
    requires n > b
    requires m(b,s,n) >= 1
    ensures S(a, b, s, w, n-s) == sum(0, m(b,s,n)-2, i => S1(a,i)*S2(s,w,n,i+1))
  {
    var mv := m(b,s,n); assert mv >= 1;
    calc { 
         S(a, b, s, w, n-s);
      == { reveal S(); lem_mmLR_mRewr(a, b, s, n); }
         sum(0, mv-2, i => S1(a,i)*S2(s,w,n-s,i));
      == { reveal S2();
            assert forall i :: 0 <= i <= mv-2 ==> 
              S1(a,i)*S2(s,w,n-s,i) == S1(a,i)*liftD(w,0.0)((n-s)-i*s);
            lem_sum_leibniz(0, mv-2, i => S1(a,i)*S2(s,w,n-s,i), 
                                     i => S1(a,i)*liftD(w,0.0)((n-s)-i*s));  }
         sum(0, mv-2, i => S1(a,i)*liftD(w,0.0)((n-s)-i*s)); 
      == { assert forall i {:trigger S1(a,i), liftD(w,0.0)((n-s)-i*s)} :: 
              0 <= i <= mv-2 ==>     S1(a,i)*liftD(w,0.0)((n-s)-i*s) 
                                  == S1(a,i)*liftD(w,0.0)(n-(i+1)*s);
            lem_sum_leibniz(0, mv-2, i => S1(a,i)*liftD(w,0.0)((n-s)-i*s), 
                                      i => S1(a,i)*liftD(w,0.0)(n-(i+1)*s));  }
         sum(0, mv-2, i => S1(a,i)*liftD(w,0.0)((n-(i+1)*s)));  
      == { reveal S2();
            assert forall i :: 0 <= i <= mv-2 ==> 
              S1(a,i)*liftD(w,0.0)(n-(i+1)*s) == S1(a,i)*S2(s,w,n,i+1);
            lem_sum_leibniz(0, mv-2, i => S1(a,i)*liftD(w,0.0)(n-(i+1)*s), 
                                     i => S1(a,i)*S2(s,w,n,i+1));  }
         sum(0, mv-2, i => S1(a,i)*S2(s,w,n,i+1));      
    }  
  }

  // m = m' - 1
  // ceil(((n-s)-b)/s) = ceil((n-b)/s) - 1
  lemma lem_mmLR_mRewr(a:nat, b:nat, s:nat, n:nat)  
    requires a > 0 && s > 0 && b >= s-1
    requires n > b
    requires m(b,s,n) >= 1
    ensures  m(b,s,n-s) == m(b,s,n) - 1
  {
    assert arith:  (((n-b)-s) as real)/(s as real) 
                == ((((n-b) as real)/(s as real)) - ((s/s) as real));
    calc {
         m(b,s,n-s);
      == { reveal m(); }
         max(0, ceil((((n-s)-b) as real)/(s as real)));
      == max(0, ceil((((n-b)-s) as real)/(s as real))); 
      == { reveal arith; }
         max(0, ceil(((((n-b) as real)/(s as real)) - ((s/s) as real)) as real));
      == max(0, ceil(((n-b) as real)/(s as real)) - 1);
      == { assert ceil(((n-b) as real)/(s as real)) - 1 >= 0; } 
         ceil(((n-b) as real)/(s as real)) - 1;
      == { assert ceil(((n-b) as real)/(s as real)) > 0; }
         max(0, ceil(((n-b) as real)/(s as real))) - 1;  
      == { reveal m(); }
         m(b,s,n) - 1;    
    }  
  }

  // ∃ d: ∀ n : S(n) <= Sbound(n,d)
  // ∃ d: ∀ n : S(n) <= d*n^k*sum_{i=0}^{m-1}a^i
  lemma {:axiom} lem_mmLR_SupBound(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, k:R0)  
    requires a > 0 && s > 0 && b >= s-1
    requires bigO(w, n => pow(n as R0, k))
    ensures exists d :: SupBoundPred(a, b, s, w, k, d)


  // A special case of thm_masterMethodLR.
  // This version doesn't admit recurrences with base case at n <= 0.
  //
  // Let T:nat->R0 be such that
  //   T(n) = / c                 , n <= b        
  //          \ a*T(n-b) + w(n)   , n > b           
  // where a>0, b>0 and w in O(n^k) for some k.    
  // Then:
  //   T(n) = / O(n^{k+1})        , a = 1
  //          \ O(n^k*a^{n/b})    , a > 1
  lemma thm_masterMethodLR2(a:nat, b:nat, c:R0, T:nat->R0, w:nat->R0, k:R0)  
    requires a > 0 && b > 0
    requires bigO(w, (n:nat) => pow(n as R0, k)) 
    requires forall n:nat :: T(n) == TbodyLR2(a, b, c, T, w, n) 

    ensures a == 1 ==> bigO(T, (n:nat) => pow(n as R0, k + 1.0))
    ensures a > 1  ==> bigO(T, (n:nat) => pow(n as R0, k)*pow(a as R0, (n/b) as R0))
  {
    // proof using thm_masterMethodLR with s := b.
    assert a > 0;   
    assert b > 0;   
    assert b >= b - 1;
    assert bigO(w, n => pow(n as R0, k));
    assert forall n:nat :: T(n) == TbodyLR2(a, b, c, T, w, n); 
    assert forall n:nat :: T(n) == TbodyLR(a, b, c, b, T, w, n)
      by { reveal TbodyLR2, TbodyLR; } 

    thm_masterMethodLR(a, b, c, b, T, w, k);
  }

  opaque ghost function TbodyLR2(a:nat, b:nat, c:R0, T:nat->R0, w:nat->R0, n:nat) : R0
  {   
    if   n <= b 
    then c
    else (a as R0)*T(n - b) + w(n)   
  }

}