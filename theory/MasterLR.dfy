include "./math/ExpReal.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemBoundsNat.dfy"
include "./math/LemFunction.dfy"
include "./math/LogReal.dfy"
include "./math/MaxMin.dfy"
include "./math/SumReal.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityR0.dfy"
include "./LemComplexityR0.dfy"

/******************************************************************************
  Master Theorem for linear recurrences
******************************************************************************/

module MasterLR {  

  import opened ExpReal 
  import opened FloorCeil
  import opened LemBoundsNat
  import opened LemFunction
  import opened LogReal
  import opened MaxMin
  import opened SumReal
  import opened TypeR0 
  import opened ComplexityR0
  import opened LemComplexityR0

  opaque ghost function TbodyLR(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, n:nat) : R0
    requires b >= s-1
  {    
    if   n <= b 
    then c
    else (a as R0)*T(n - s) + w(n)    
  }   

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
    requires w in O(n => exp(n as R0, k))
    requires forall n:nat :: T(n) == TbodyLR(a, b, c, s, T, w, n) 

    ensures a == 1 ==> T in O((n:nat) => exp(n as R0, k + 1.0))
    ensures a > 1  ==> T in O((n:nat) => exp(n as R0, k)*exp(a as R0, n as R0 / s as R0))
  {
    // Prove: ∀ n : T(n) = a^m*c + S(n) where m=max(0,ceil((n-b)/s))
    assert forall n:nat :: T(n) == TsumForm(a, b, c, s, w, n)
      by { lem_mmLR_sumForm(a, b, c, s, T, w); }

    var d:R0, n0:nat :| bigOfrom(d, n0, w, n => exp(n as R0, k));
    if n0 <= b+s {

    } else {
      var n1 := n0+b+s+1;
      // Prove: ∀ n >= n1 : S(n) = S1(n) + S1(n) 
      assert forall n:nat :: S(a, b, s, w, n) == S1(a, b, s, w, n0, n) + S2(a, b, s, w, n0, n)
        by { lem_mmLR_splitS(a, b, s, w, n0); }

      // Prove: ∀ n >= n1 : S(n) <= SupBound1(n) + SupBound2(n)
      assert forall n:nat :: n >= n0 ==> SupBoundPred(a, b, s, w, k, d, n0, n)
        by { lem_mmLR_SupBound(a, b, c, s, T, w, k, d, n0); }

      // Prove: ∀ n >= n1 : T(n) <= a^m*c + SupBound1(n) + SupBound2(n)  
      assert forall n:nat :: n >= n1 ==> T(n) <= exp(a as R0, m(b,s,n) as real)*c + SupBound(a, b, s, w, k, d, n0, n)
        by { reveal TsumForm, SupBoundPred, SupBound; }

      if a == 1 {    
        var n:nat :| n >= n1;
        assume T(n) <= c + d*exp(n as R0, k)*(j(b,s,n0,n) as R0) + wMax(b,s,w,n,n0)*((m(b,s,n)-j(b,s,n0,n)) as R0);
          //by { reveal    } 
        assert T(n) <= c + d*exp(n as R0, k)*(j(b,s,n0,n) as R0) + wMax(b,s,w,n,n0)*(m(b,s,n) as R0);
        
  
      } else {

      }
    }

    // var n:nat :| true;
    // if n <= b {
    //   assert T(n) == c by { reveal TbodyLR; }

    //   if a == 1 {
    //     assert bigO(T, n => exp(n as R0, k + 1.0)) 
    //       by { lem_bigO_constGrowth(T, c); } 
    //   } else {

    //   }
    // } else {
    //   // 2. Prove: ∀ n >= n0 : S(n) = S1(n) + S1(n) 
    //   var d:R0, n0:nat :| bigOfrom(d, n0, w, n => exp(n as R0, k));
    //   assert n >= n0 ==> S(a, b, s, w, n) == S1(a, b, s, w, n0, n) + S2(a, b, s, w, n0, n)
    //     by { lem_mmLR_splitS(a, b, s, w, n0, n); }

    //   // 3. Prove: ∀ n >= n_0 : S(n) <= SupBound1(n) + SupBound2(n)
    //   assert n >= n0 ==> SupBoundPred(a, b, s, w, k, d, n0, n)
    //     by { lem_mmLR_SupBound(a, b, c, s, T, w, k, d, n0, n); }

    //   // Cases on "a":
    //   if a == 1 {    
    //   //     assert sumr(0, m-1, i => powr(a as R0, i as real)) == m;
    //   //     assert bigOR0(n => m, n => powr(n as R0, 1.0));
    //   //
    //     assert bigO(T, (n:nat) => exp(n as R0, k + 1.0));
    //   } else {
    //   //     assert sumr(0, m-1, i => powr(a as R0, i as real)) == ...;
    //   //     assert bigOR0(n => ..., n => powr(a as R0, (n/s) as R0));
    //   //      
    //     assert bigO(T, (n:nat) => exp(n as R0, k)*exp(a as R0, (n/s) as R0));
    //   }
    // }
  }

  // Expression: max(0, ceil((n-b)/s))
  opaque ghost function m(b:nat, s:nat, n:nat) : int
    requires s > 0
  {    
    max(0, ceil(((n-b) as real)/(s as real)))  
  } 

  // Expression: a^m*c + S(n) 
  opaque ghost function TsumForm(a:nat, b:nat, c:R0, s:nat, w:nat->R0, n:nat) : real
    requires s > 0
  {    
    exp(a as R0, m(b,s,n) as real)*c + S(a, b, s, w, n)    
  } 

  // Expression: a^i
  opaque ghost function Sa(a:nat, i:int) : real
  {    
    exp(a as R0, i as real)     
  } 

  // Expression: w(n-i*s)
  opaque ghost function Sw(s:nat, w:nat->R0, n:nat, i:int) : real
  {    
    liftD(w,0.0)(n-i*s)
  } 

  // Expression: Σ_{i=0}^{m-1}a^i*w(n-i*s)
  opaque ghost function S(a:nat, b:nat, s:nat, w:nat->R0, n:nat) : real
    requires s > 0
  {    
    sum(0, m(b,s,n)-1, i => Sa(a,i)*Sw(s,w,n,i))      
  } 

  // Expression: Σ_{i=0}^{j-1}a^i*w(n-i*s)
  opaque ghost function S1(a:nat, b:nat, s:nat, w:nat->R0, n0:nat, n:nat) : real
    requires s > 0 && b >= s-1 && n >= n0 && n > b
  {    
    sum(0, j(b,s,n0,n)-1, i => Sa(a,i)*Sw(s,w,n,i))      
  }   

  // Expression: Σ_{i=j}^{m-1}a^i*w(n-i*s)
  opaque ghost function S2(a:nat, b:nat, s:nat, w:nat->R0, n0:nat, n:nat) : real
    requires s > 0 && b >= s-1 && n >= n0 && n > b
  {    
    sum(j(b,s,n0,n), m(b,s,n)-1, i => Sa(a,i)*Sw(s,w,n,i))      
  }    

  // Expression: d*n^k*Σ_{i=0}^{j-1}a^i
  opaque ghost function SupBound1(a:nat, b:nat, s:nat, w:nat->R0, k:R0, d:R0, n0:nat, n:nat) : real
    requires s > 0 && b >= s-1 && n >= n0 && n > b
  {    
    d*exp(n as R0, k)*sum(0, j(b,s,n0,n)-1, i => Sa(a,i))    
  } 

  // Expression: wMax*Σ_{i=i0}^{m-1}a^i 
  opaque ghost function SupBound2(a:nat, b:nat, s:nat, w:nat->R0, n0:nat, n:nat) : real
    requires s > 0 && b >= s-1 && n >= n0 && n > b
  {    
    wMax(b,s,w,n,n0)*sum(j(b,s,n0,n), m(b,s,n)-1, i => Sa(a,i))    
  } 

  // Expression: d*n^k*Σ_{i=0}^{i0-1}a^i + wMax*Σ_{i=i0}^{m-1}a^i 
  opaque ghost function SupBound(a:nat, b:nat, s:nat, w:nat->R0, k:R0, d:R0, n0:nat, n:nat) : real
    requires s > 0 && b >= s-1 && n >= n0 && n > b
  {    
    SupBound1(a, b, s, w, k, d, n0, n) + SupBound2(a, b, s, w, n0, n)
  } 

  // Predicate: S(n) <= SupBound(n,d)
  ghost predicate SupBoundPred(a:nat, b:nat, s:nat, w:nat->R0, k:R0, d:R0, n0:nat, n:nat)
    requires s > 0 && b >= s-1 && n >= n0 && n > b
  {    
    S(a, b, s, w, n) <= SupBound(a, b, s, w, k, d, n0, n)
  } 

  // Expression: wMax
  opaque ghost function wMax(b:nat, s:nat, w:nat->R0, n:nat, n0:nat) : R0
    requires s > 0
  {    
    0.0
  }   

  // Expression: min(i0, m-1)
  opaque ghost function j(b:nat, s:nat, n0:nat, n:nat) : nat
    requires s > 0 && b >= s-1 && n >= n0 && n > b
  {
    lem_mmLR_mValue(b, s, n);
    min(i0(s,n0,n), m(b,s,n)-1)
  }   

  // Expression: i0
  opaque ghost function i0(s:nat, n0:nat, n:nat) : nat
    requires s > 0 && n >= n0
  {
    floor(((n-n0) as real)/(s as real)) + 1
  }   

  // Expression: n1
  // opaque ghost function n1(b:nat, s:nat, n0:nat) : nat
  //   requires s > 0 && b >= s-1
  // {    
  //   lem_mmLR_mValue(b, s, n0);
  //   n0 + m(b,s,n0)*s
  // } 

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
           lem_ceilxLEQnIFFxLEQn(((n-b) as real)/(s as real), 0); }
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
            lem_ceilxLEQnIFFxLEQn(((n-b) as real)/(s as real), 0); }
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

  // ∀ n : T(n) = a^m*c + Σ_{i=0}^{m-1}a^i*w(n-i*s) where m=ceil((n-b)/s)
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
        == { lem_mmLR_mValue(b, s, n); lem_exp_Zero(aR); }
           exp(aR, mv as real)*c + S(a, b, s, w, n);
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
                      == sum(0, mv-2, i => Sa(a,i)*Sw(s,w,n,i+1))
        by { lem_mmLR_sumRewr(a, b, c, s, T, w, n); }
      assert sumRewr2:   aR*sum(0, mv-2, i => Sa(a,i)*Sw(s,w,n,i+1))
                      == sum(0, mv-2, i => Sa(a,i+1)*Sw(s,w,n,i+1))
        by { lem_mmLR_sumRewr2(a, b, c, s, T, w, n); }  
      assert sumRewr3:   sum(0, mv-2, i => Sa(a,i+1)*Sw(s,w,n,i+1))  
                      == sum(1, mv-1, i => Sa(a,i)*Sw(s,w,n,i))
        by { lem_mmLR_sumRewr3(a, b, c, s, T, w, n); }
      assert wRewr: w(n) == Sa(a,0)*Sw(s,w,n,0)
        by {
          calc {
               Sa(a,0)*Sw(s,w,n,0);
            == { reveal Sw(); } 
               Sa(a,0)*liftD(w,0.0)(n-0*s);
            == { reveal Sa(); } 
               exp(a as R0, 0 as real)*liftD(w,0.0)(n-0*s); 
            == { lem_exp_Zero(a as R0); }    
               1.0*liftD(w,0.0)(n-0*s); 
            == { lem_exp_Zero(a as R0); }    
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
           aR*(exp(aR, mv' as real)*c + S(a, b, s, w, n-s)) + w(n);  
        == { reveal mRewr; }
           aR*(exp(aR, (mv-1) as real)*c + S(a, b, s, w, n-s)) + w(n); 
        == aR*exp(aR, (mv-1) as real)*c + aR*S(a, b, s, w, n-s) + w(n); 
        == { lem_exp_Def(aR, (mv-1) as real); }
           exp(aR, mv as real)*c + aR*S(a, b, s, w, n-s) + w(n);     
        == { reveal sumRewr; }
           exp(aR, mv as real)*c + aR*sum(0, mv-2, i => Sa(a,i)*Sw(s,w,n,i+1)) + w(n);
        == { reveal sumRewr2; }
           exp(aR, mv as real)*c + sum(0, mv-2, i => Sa(a,i+1)*Sw(s,w,n,i+1)) + w(n);    
        == { reveal sumRewr3; }
           exp(aR, mv as real)*c + sum(1, mv-1, i => Sa(a,i)*Sw(s,w,n,i)) + w(n); 
        == { reveal wRewr; }
           exp(aR, mv as real)*c + sum(1, mv-1, i => Sa(a,i)*Sw(s,w,n,i)) + Sa(a,0)*Sw(s,w,n,0); 
        == { reveal sum(); }
           exp(aR, mv as real)*c + sum(0, mv-1, i => Sa(a,i)*Sw(s,w,n,i));           
        == { reveal TsumForm(), S(); }
           TsumForm(a, b, c, s, w, n);                                                                   
      }  
    } 
  }

  lemma lem_mmLR_sumRewr3(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, n:nat)  
    requires a > 0 && s > 0 && b >= s-1
    requires n > b
    requires m(b,s,n) >= 1
    ensures    sum(0, m(b,s,n)-2, i => Sa(a,i+1)*Sw(s,w,n,i+1))  
            == sum(1, m(b,s,n)-1, i => Sa(a,i)*Sw(s,w,n,i))
  {
    var mv := m(b,s,n); assert mv >= 1;
    calc {
         sum(0, mv-2, i => Sa(a,i+1)*Sw(s,w,n,i+1));
      == { lem_sum_shiftIndex(0, mv-2, 1, i => Sa(a,i+1)*Sw(s,w,n,i+1)); } 
         sum(1, mv-1, l => (i => Sa(a,i+1)*Sw(s,w,n,i+1))(l-1)); 
      == { reveal Sw();
           assert forall l :: 1 <= l <= mv-1 ==> 
             (i => Sa(a,i+1)*Sw(s,w,n,i+1))(l-1) == Sa(a,l)*Sw(s,w,n,l);
           lem_sum_leibniz(1, mv-1, l => (i => Sa(a,i+1)*Sw(s,w,n,i+1))(l-1), 
                                    l => Sa(a,l)*Sw(s,w,n,l)); } 
         sum(1, mv-1, i => Sa(a,i)*Sw(s,w,n,i));            
    }      
  }

  lemma {:isolate_assertions} lem_mmLR_sumRewr2(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, n:nat)  
    requires a > 0 && s > 0 && b >= s-1
    requires n > b
    requires m(b,s,n) >= 1
    ensures    (a as R0)*sum(0, m(b,s,n)-2, i => Sa(a,i)*Sw(s,w,n,i+1))
            == sum(0, m(b,s,n)-2, i => Sa(a,i+1)*Sw(s,w,n,i+1))
  {
    var mv := m(b,s,n); assert mv >= 1;
    var aR := a as R0;
      calc {
           aR*sum(0, mv-2, i => Sa(a,i)*Sw(s,w,n,i+1));
        == { lem_sum_linearityConst(0, mv-2, aR, i => Sa(a,i)*Sw(s,w,n,i+1)); }
           sum(0, mv-2, l => aR*(i => Sa(a,i)*Sw(s,w,n,i+1))(l)); 
        == { reveal Sa(); assert aR == a as real;
             assert forall l :: 0 <= l <= mv-2 ==> 
               aR*(i => Sa(a,i)*Sw(s,w,n,i+1))(l) == aR*exp(a as real,l as real)*Sw(s,w,n,l+1);
             lem_sum_leibniz(0, mv-2, l => aR*(i => Sa(a,i)*Sw(s,w,n,i+1))(l), 
                                      l => aR*exp(a as real,l as real)*Sw(s,w,n,l+1)); } 
           sum(0, mv-2, i => aR*exp(aR,i as real)*Sw(s,w,n,i+1));  
        == { reveal Sa(); lem_exp_DefAuto();
             assert forall l :: 0 <= l <= mv-2 ==> 
               aR*exp(aR,l as real)*Sw(s,w,n,l+1) == Sa(a,l+1)*Sw(s,w,n,l+1);
             lem_sum_leibniz(0, mv-2, i => aR*exp(aR,i as real)*Sw(s,w,n,i+1), 
                                      i => Sa(a,i+1)*Sw(s,w,n,i+1)); }       
           sum(0, mv-2, i => Sa(a,i+1)*Sw(s,w,n,i+1));       
      }         
  }

  lemma lem_mmLR_sumRewr(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, n:nat)  
    requires a > 0 && s > 0 && b >= s-1
    requires n > b
    requires m(b,s,n) >= 1
    ensures  S(a, b, s, w, n-s) == sum(0, m(b,s,n)-2, i => Sa(a,i)*Sw(s,w,n,i+1))
  {
    var mv := m(b,s,n); assert mv >= 1;
    calc { 
         S(a, b, s, w, n-s);
      == { reveal S(); lem_mmLR_mRewr(a, b, s, n); }
         sum(0, mv-2, i => Sa(a,i)*Sw(s,w,n-s,i));
      == { reveal Sw();
           assert forall i :: 0 <= i <= mv-2 ==> 
             Sa(a,i)*Sw(s,w,n-s,i) == Sa(a,i)*liftD(w,0.0)((n-s)-i*s);
           lem_sum_leibniz(0, mv-2, i => Sa(a,i)*Sw(s,w,n-s,i), 
                                    i => Sa(a,i)*liftD(w,0.0)((n-s)-i*s));  }
         sum(0, mv-2, i => Sa(a,i)*liftD(w,0.0)((n-s)-i*s)); 
      == { assert forall i {:trigger Sa(a,i), liftD(w,0.0)((n-s)-i*s)} :: 
             0 <= i <= mv-2 ==>     Sa(a,i)*liftD(w,0.0)((n-s)-i*s) 
                                 == Sa(a,i)*liftD(w,0.0)(n-(i+1)*s);
           lem_sum_leibniz(0, mv-2, i => Sa(a,i)*liftD(w,0.0)((n-s)-i*s), 
                                    i => Sa(a,i)*liftD(w,0.0)(n-(i+1)*s));  }
         sum(0, mv-2, i => Sa(a,i)*liftD(w,0.0)((n-(i+1)*s)));  
      == { reveal Sw();
           assert forall i :: 0 <= i <= mv-2 ==> 
             Sa(a,i)*liftD(w,0.0)(n-(i+1)*s) == Sa(a,i)*Sw(s,w,n,i+1);
           lem_sum_leibniz(0, mv-2, i => Sa(a,i)*liftD(w,0.0)(n-(i+1)*s), 
                                    i => Sa(a,i)*Sw(s,w,n,i+1));  }
         sum(0, mv-2, i => Sa(a,i)*Sw(s,w,n,i+1));      
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
    assert arith:   (((n-b)-s) as real)/(s as real) 
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

  // n0 > b ==> ∀ n >= n0 : S(n) = S1(n) + S1(n) 
  lemma lem_mmLR_splitS(a:nat, b:nat, s:nat, w:nat->R0, n0:nat)  
    requires a > 0 && s > 0 && b >= s-1 // && n0 > b+s
    ensures  forall n:nat :: n >= n0 ==> S(a, b, s, w, n) == S1(a, b, s, w, n0, n) + S2(a, b, s, w, n0, n)
  {
    forall n:nat | n >= n0 // n >= n0
      ensures S(a, b, s, w, n) == S1(a, b, s, w, n0, n) + S2(a, b, s, w, n0, n)
    {
      reveal S, S1, S2;
      var mv  := m(b,s,n); 
      //var i0v := i0(s,n0,n);
      var jv  := j(b,s,n0,n);

      lem_mmLR_mValue(b, s, n);
      assert mv == ceil(((n-b) as real)/(s as real));
      assert mv >= 1;
       
      // assert n-n0 < n-b; 
      // assert n-n0 < n-(b+1);
      // assert n-n0 +1 <= n-b - 1;
      // assert floor(((n-n0) as real)/(s as real)) < ceil(((n-b) as real)/(s as real));
      // assert floor(((n-n0) as real)/(s as real)) +1 <= ceil(((n-b) as real)/(s as real))-1;

      // var x:nat, y:nat :| true;
      // assume x <= y;
      // assert floor(x as real) <= ceil(y as real);
      // lem_floorCeilMonoDiv(x as real, y as real, s as real);
      // assert floor(x as real / s as real) <= ceil(y as real / s as real);
      // //assert floor(x as real / s as real) <= ceil(y as real / s as real) - 1;

      // assert ((n-n0) as real)/(s as real) + 2 as real <= ((n-b) as real)/(s as real) + 1 as real;
      // assert floor(((n-n0) as real)/(s as real)) + 2 <= ceil(((n-b) as real)/(s as real));

      //   calc {
      //          n - n0 < n - (b + 1);
      //     <==> n - n0 < (n - b) - 1;
      //     <==> n - n0 + 1 <= n - b - 1;
      //     <==> n - n0 + 1 <= n - b - 1;
      //     <==> { assert n-n0  <= n-b;
      //            lem_floorCeilMonoDiv((n-n0) as real, (n-b) as real, s as real);
      //            assert floor(((n-n0) as real)) <= ceil(((n-b) as real));
      //            assert floor(((n-n0) as real)/(s as real)) <= ceil(((n-b) as real)/(s as real)); }
      //          floor(((n-n0) as real)/(s as real)) + 1 <= ceil(((n-b) as real)/(s as real)) - 1;
      //   }

      // // assert i0v <= mv-1 by {


      // // }

      assert 0 <= jv <= mv-1 by { reveal m, j, i0; }
      lem_sum_split2(0, mv-1, jv, i => Sa(a,i)*Sw(s,w,n,i));
    }
  }

  // When n0 > b.
  // ∀ n >= n0 : S(n) <= SupBound(n)
  //                   = d*n^k*Σ_{i=0}^{i0-1}a^i + wMax*Σ_{i=i0}^{m-1}a^i
  lemma {:axiom} lem_mmLR_SupBound(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, k:R0, d:R0, n0:nat)  
    requires a > 0 && s > 0 && b >= s-1 && n0 > b
    requires bigOfrom(d, n0, w, n => exp(n as R0, k))
    ensures  forall n :: n >= n0 ==> SupBoundPred(a, b, s, w, k, d, n0, n)
  //{}

  // ∀ n >= n1 : S(n) <= Sbound(n,d)
  //                   = d*n^k*Σ_{i=0}^{m-1}a^i
  // lemma {:axiom} lem_mmLR_SupBound(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, k:R0, d:R0, n0:nat)  
  //   requires a > 0 && s > 0 && b >= s-1
  //   //requires bigO(w, n => pow(n as R0, k))
  //   requires bigOfrom(d, n0, w, n => exp(n as R0, k))
  //   ensures  forall n:nat :: n >= n1(b,s,n0) ==> SupBoundPred(a, b, s, w, k, d, n)
  // {
  //   assert AA: forall n:nat :: 0 <= n0 <= n ==> w(n) <= d*exp(n as R0, k);

  //   forall n:nat | n >= n1(b,s,n0)
  //     ensures SupBoundPred(a, b, s, w, k, d, n)
  //   {
  //     var mv := m(b,s,n); 
  //     assert mv >= 0 by { lem_mmLR_mValue(b,s,n); }
  //     assert AB: n0 <= n1(b,s,n0) by { reveal n1, m; }
  //     assert AC: forall i:nat :: 0 <= i <= mv-1 ==> n1(b,s,n0) <= n-i*s by { reveal n1, m; }

  //     assert A: forall i :: 0 <= i <= mv-1 ==> Sw(s,w,n,i) <= d*exp(n as R0, k) by {
  //       forall i:nat | 0 <= i <= mv-1
  //         ensures Sw(s,w,n,i) <= d*exp(n as R0, k)
  //       {         
  //         if n - i*s < 0 {
  //           calc {
  //                Sw(s,w,n,i);
  //             == { reveal Sw(); }
  //                0.0;
  //             <= d*exp(n as R0, k);   
  //           }            
  //         } else {
  //           calc {
  //                Sw(s,w,n,i);
  //             == { reveal Sw(); }
  //                w(n - i*s); 
  //             <= { reveal AA, AB, AC; }
  //                d*exp((n - i*s) as R0, k);
  //             <= { lem_expBaseMono(k, (n - i*s) as R0, n as R0); }
  //                d*exp(n as R0, k);    
  //           }   
  //         }
  //       }
  //     }    
  //     assert B: forall i :: 0 <= i <= mv-1 ==> Sa(a,i) >= 0.0 by {
  //       reveal S1;
  //     }      

  //     calc {
  //          S(a, b, s, w, n);
  //       == { reveal S(); }
  //          sum(0, mv-1, i => Sa(a,i)*Sw(s,w,n,i));  
  //       <= { assert forall i :: 0 <= i <= mv-1 ==> 
  //              Sa(a,i)*Sw(s,w,n,i) <= Sa(a,i)*(d*exp(n as R0, k)) 
  //                by { reveal A, B; }
  //            lem_sum_mono(0, mv-1, i => Sa(a,i)*Sw(s,w,n,i), 
  //                                  i => Sa(a,i)*(d*exp(n as R0, k))); }
  //          sum(0, mv-1, i => Sa(a,i)*(d*exp(n as R0, k)));  
  //       == { assert forall l :: 0 <= l <= mv-1 ==> 
  //              Sa(a,l)*(d*exp(n as R0, k)) == (d*exp(n as R0, k))*(i => Sa(a,i))(l);
  //            lem_sum_leibniz(0, mv-1, l => Sa(a,l)*(d*exp(n as R0, k)), 
  //                                     l => (d*exp(n as R0, k))*(i => Sa(a,i))(l)); }
  //          sum(0, mv-1, l => (d*exp(n as R0, k))*(i => Sa(a,i))(l)); 
  //       == { lem_sum_linearityConst(0, mv-1, d*exp(n as R0, k), i => Sa(a,i)); }
  //          d*exp(n as R0, k)*sum(0, mv-1, i => Sa(a,i));  
  //       == { reveal SupBound(); }
  //          SupBound(a, b, s, w, k, n, d);     
  //     }
  //   }  
  // }

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

  opaque ghost function TbodyLR2(a:nat, b:nat, c:R0, T:nat->R0, w:nat->R0, n:nat) : R0
  {   
    if   n <= b 
    then c
    else (a as R0)*T(n - b) + w(n)   
  }

  lemma thm_masterMethodLR2(a:nat, b:nat, c:R0, T:nat->R0, w:nat->R0, k:R0)  
    requires a > 0 && b > 0
    requires w in O((n:nat) => exp(n as R0, k)) 
    requires forall n:nat :: T(n) == TbodyLR2(a, b, c, T, w, n) 

    ensures a == 1 ==> T in O((n:nat) => exp(n as R0, k + 1.0))
    ensures a > 1  ==> T in O((n:nat) => exp(n as R0, k)*exp(a as R0, n as R0 / b as R0))
  {
    // proof using thm_masterMethodLR with s := b.
    assert a > 0;   
    assert b > 0;   
    assert b >= b - 1;
    assert w in O(n => exp(n as R0, k));
    assert forall n:nat :: T(n) == TbodyLR2(a, b, c, T, w, n); 
    assert forall n:nat :: T(n) == TbodyLR(a, b, c, b, T, w, n)
      by { reveal TbodyLR2, TbodyLR; } 

    thm_masterMethodLR(a, b, c, b, T, w, k);
  }

}