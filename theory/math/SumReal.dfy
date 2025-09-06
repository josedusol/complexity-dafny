/******************************************************************************
  Sum over integer intervals and real codomain
******************************************************************************/

module SumReal {

  // sum_{k=a}^{b}f(k)
  opaque ghost function sum(a:int, b:int, f:int->real): real
    decreases b - a
  {
    if a > b  
    then 0.0
    else f(a) + sum(a+1, b, f)
  }

  // a <= b+1 ==> sum_{k=a}^{b+1}f(k) = sum_{k=a}^{b}f(k) + f(b+1)
  lemma lem_sum_dropLast(a:int, b:int, f:int->real)
    requires a <= b+1
    ensures  sum(a, b+1, f) == sum(a, b, f) + f(b+1) 
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           sum(b+1, b+1, f);
        == { reveal sum(); }
           f(b+1);
        == 0.0 + f(b+1) ;
        == { reveal sum(); }
           sum(a, b, f) + f(b+1) ;       
      }
    } else {  
      // Step. a <= j
      //   IH: sum(a+1, b+1, f) = sum(a+1, b, f) + f(b+1)
      //    T: sum(a, b+1, f)   = sum(a, b, f)   + f(b+1)
      calc {  
           sum(a, b+1, f);
        == { reveal sum(); } 
           f(a) + sum(a+1, b+1, f);
        == { lem_sum_dropLast(a+1, b, f); }  // by IH
           f(a) + (sum(a+1, b, f) + f(b+1));
        == (f(a) + sum(a+1, b, f)) + f(b+1);
        == { reveal sum(); }
          sum(a, b, f) + f(b+1);           
      }
    }
  } 

  lemma lem_sum_dropLastAll(a:int, b:int)
    requires a <= b+1
    ensures  forall f:int->real :: sum(a, b+1, f) == sum(a, b, f) + f(b+1) 
  { 
    forall f:int->real
      ensures sum(a, b+1, f) == sum(a, b, f) + f(b+1) 
    {
      lem_sum_dropLast(a, b, f);
    }
  }

  // i <= j+1 ==> c*sum_{k=i}^{j}f(k) = sum_{k=i}^{j}c*f(k)
  lemma lem_sum_linearityConst(a:int, b:int, c:real, f:int->real)
    requires a <= b+1
    ensures  c*sum(a, b, f) == sum(a, b, k => c*f(k))
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           c*sum(b+1, b, f);
        == { reveal sum(); }
           0.0;
        == { reveal sum(); }
           sum(b+1, b, k => c*f(k));       
      }
    } else {  
      // Step. a <= b
      //   IH: c*sum(a+1, b, f) = c*sum(a+1, b, k => c*f(k))
      //    T: c*sum(a, b, f)   = c*sum(a, b, k => f(k))
      calc {  
           c*sum(a, b, f);
        == { reveal sum(); } 
           c*(f(a) + sum(a+1, b, f));
        == c*f(a) + c*sum(a+1, b, f);         
        == { lem_sum_linearityConst(a+1, b, c, f); }  // by IH
           c*f(a) + sum(a+1, b, k => c*f(k)); 
        == (k => c*f(k))(a) + sum(a+1, b, k => c*f(k));
        == { reveal sum(); } 
           sum(a, b, k => c*f(k));           
      } 
    }  
  }

  // a <= b+1 ==> sum_{k=a}^{b}c = c*(b - a + 1)
  lemma lem_sum_const(a:int, b:int, c:real)
    requires a <= b+1
    ensures  sum(a, b, k => c) == c * (b - a + 1) as real
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           sum(b+1, b, k => c); 
        == { reveal sum(); } 
           0.0; 
        == (b - (b+1) + 1) as real;
      }
    } else {  
      // Step. a <= b
      //   IH: sum(a+1, b, k => c) = c*(b - (a+1) + 1) = c*(b - a)
      //    T: sum(a, b, k => c)   = c*(b - a + 1) 
      calc {  
           sum(a, b, k => c);
        == { reveal sum(); }
           c + sum(a+1, b, x => c);
        == { lem_sum_const(a+1, b, c); }  // by IH
           (c + c* (b - (a+1) + 1) as real);
        == c + c*((b - a) as real);      
        == c* (b - a + 1) as real;             
      }
    }
  }

  lemma lem_sum_constAll(a:int, b:int)
    requires a <= b+1
    ensures  forall c:real :: sum(a, b, k => c) == c * (b - a + 1) as real
  { 
    forall c:real
      ensures sum(a, b, k => c) == c * (b - a + 1) as real
    {
      lem_sum_const(a, b, c);
    }
  } 

  // a <= b+1 ==> sum_{k=a}^{b}f(k) = sum_{k=a+d}^{b+d}f(k-d)
  lemma lem_sum_shiftIndex(a:int, b:int, d:int, f:int->real)
    requires a <= b+1
    ensures  sum(a, b, f) == sum(a+d, b+d, k => f(k-d))
    decreases b - a
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           sum(b+1, b, f);
        == { reveal sum(); }
           0.0;
        == { reveal sum(); }
           sum(b+1+d, b+d, k => f(k-d));       
      }
    } else {  
      // Step. a <= b
      //   IH: sum(a+1, b, f) = sum((a+d)+1, b+d, k => f(k-d))
      //    T: sum(a, b, f)   = sum(a+d, b+d, k => f(k-d))
      calc {  
           sum(a, b, f);
        == { reveal sum(); } 
           f(a) + sum(a+1, b, f);
        == { lem_sum_shiftIndex(a+1, b, d, f); }  // by IH
           f(a) + sum(a+1+d, b+d, k => f(k-d));
        == (k => f(k-d))(a+d) + sum((a+d)+1, b+d, k => f(k-d));
        == { reveal sum(); }
           sum(a+d, b+d, k => f(k-d));           
      }
    }
  } 

  // a <= b+1 ==> sum_{k=a}^{b}k = (b*(b+1) + a*(1-a))/2 
  lemma lem_sum_interval(a:int, b:int)
    requires a <= b+1 
    decreases b - a
    ensures sum(a, b, k => k as real) == (b*(b+1) + a*(1-a)) as real / 2.0
  { 
    if a == b+1 {   
      // BC: a > b
      calc {
           sum(b+1, b, k => k as real);
        == { reveal sum(); }
           0.0;
        == (b*(b+1) + ((b+1))*(1-((b+1)))) as real / 2.0;
      }
    } else {  
      // Step. a <= b
      //   IH: sumr(a+1, b, K => k) = (b*(b+1) + (a+1)*(1-(a+1)))/2 
      //    T: sumr(a, b, k => k)   = (b*(b+1) + a*(1-a))/2 
      calc {  
           sum(a, b, k => k as real);
        == { reveal sum(); }
           a as real + sum(a+1, b, k => k as real);
        == { lem_sum_interval(a+1, b); }  // by IH
           a as real + (b*(b+1) + (a+1)*(1-(a+1))) as real / 2.0;
        == (b*(b+1) + a*(1-a)) as real / 2.0;            
      }
    } 
  }

  // a <= b+1 /\ (∀ k : a<=k<=b : f(k) == g(k)) 
  //          ==> sum_{k=a}^{b}f = sum_{k=a}^{b}g
  lemma lem_sum_leibniz(a:int, b:int, f:int->real, g:int->real)
    requires a <= b+1
    requires forall k:int :: a<=k<=b ==> f(k) == g(k)
    ensures sum(a, b, f) == sum(a, b, g)
    decreases b - a
  {
    if a == b+1 {   
      // BC: a > b
      calc {
           sum(b+1, b, f);
        == { reveal sum(); }
           0.0;
        == { reveal sum(); }
           sum(b+1, b, g);       
      }
    } else {  
      // Step. a <= b
      //   IH: sum(a+1, b, f) = sum(a+1, b, g)
      //    T: sum(a, b, f)   = sum(a, b, g)
      calc {  
           sum(a, b, f);
        == { reveal sum(); } 
           f(a) + sum(a+1, b, f);
        == g(a) + sum(a+1, b, f);
        == { lem_sum_leibniz(a+1, b, f, g); }  // by IH
           g(a) + sum(a+1, b, g);
        == { reveal sum(); }
           sum(a, b, g);           
      }
    }
  } 

  // a <= b+1 /\ (∀ k : a<=k<=b : f(k) <= g(k)) 
  //          ==> sum_{k=a}^{b}f <= sum_{k=a}^{b}g
  lemma lem_sum_mono(a:int, b:int, f:int->real, g:int->real)
    requires a <= b+1
    requires forall k:int :: a<=k<=b ==> f(k) <= g(k)
    ensures sum(a, b, f) <= sum(a, b, g)
    decreases b - a
  {
    if a == b+1 {   
      // BC: a > b
      calc {
           sum(b+1, b, f);
        == { reveal sum(); }
           0.0;
        == { reveal sum(); }
           sum(b+1, b, g);       
      }
    } else {  
      // Step. a <= b
      //   IH: sum(a+1, b, f) <= sum(a+1, b, g)
      //    T: sum(a, b, f)   <= sum(a, b, g)
      calc {  
           sum(a, b, f);
        == { reveal sum(); } 
           f(a) + sum(a+1, b, f);
        <= { assert f(a) <= g(a);  }
           g(a) + sum(a+1, b, f);
        <= { lem_sum_mono(a+1, b, f, g); }  // by IH
           g(a) + sum(a+1, b, g);
        == { reveal sum(); }
           sum(a, b, g);           
      }
    }
  } 

  // a<=j<=b ==> sum_{k=a}^{b}f = sum_{k=a}^{j}f + sum_{k=j+1}^{b}f
  lemma lem_sum_split(a:int, b:int, j:int, f:int->real)
    requires a <= j <= b
    ensures sum(a, b, f) == sum(a, j, f) + sum(j+1, b, f)
    decreases b - a
  {
    if a == b+1 {
      // BC: a > b 
      assert true; // trivial
    } else {  
      // Step. a <= b
      //   IH: sum(a+1, b, f) = sum(a+1, j, f) + sum(j+1, b, f)
      //    T: sum(a, b, f)   = sum(a, j, f) + sum(j+1, b, f)
      if a == j {
        calc {  
             sum(j, b, f);
          == { reveal sum(); } 
             f(j) + sum(j+1, b, f);
          == { reveal sum(); } 
             sum(j, j, f) + sum(j+1, b, f);   
        }
      } else if a < j {
        calc {  
             sum(a, b, f);
          == { reveal sum(); } 
             f(a) + sum(a+1, b, f);
          == { lem_sum_split(a+1, b, j, f); }  // by IH
             f(a) + (sum(a+1, j, f) + sum(j+1, b, f));
          == (f(a) + sum(a+1, j, f)) + sum(j+1, b, f);
          == { reveal sum(); } 
             sum(a, j, f) + sum(j+1, b, f);        
        }
      }
    }
  } 

  // a<=j<=b ==> sum_{k=a}^{b}f = sum_{k=a}^{j-1}f + sum_{k=j}^{b}f
  lemma lem_sum_split2(a:int, b:int, j:int, f:int->real)
    requires a <= j <= b
    ensures sum(a, b, f) == sum(a, j-1, f) + sum(j, b, f)
    decreases b - a
  {
    calc {
         sum(a, b, f);
      == { lem_sum_split(a, b, j, f); } 
         sum(a, j, f) + sum(j+1, b, f);
      == { lem_sum_dropLast(a, j-1, f); }
         (sum(a, j-1, f) + f(j)) + sum(j+1, b, f); 
      == sum(a, j-1, f) + (f(j) + sum(j+1, b, f));      
      == { reveal sum; }
         sum(a, j-1, f) + sum(j, b, f);
    }
  }

}