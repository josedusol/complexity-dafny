include "./math.dfy"

/**************************************************************************
  Sum over integer intervals
**************************************************************************/

// sum_{k=a}^{b}f(k)
opaque ghost function sumr(a:int, b:int, f:int->real): real
  decreases b - a
{
  if a > b  
  then 0.0
  else f(a) + sumr(a+1, b, f)
}

// a <= b+1 ==> sum_{k=a}^{b+1}f(k) = sum_{k=a}^{b}f(k) + f(b+1)
lemma lem_sumr_dropLast(a:int, b:int, f:int->real)
  requires a <= b+1
  ensures  sumr(a, b+1, f) == sumr(a, b, f) + f(b+1) 
  decreases b - a
{ 
  if a == b+1 {   
    // BC: a > b
    calc {
         sumr(b+1, b+1, f);
      == { reveal sumr(); }
         f(b+1);
      == 0.0 + f(b+1) ;
      == { reveal sumr(); }
         sumr(a, b, f) + f(b+1) ;       
    }
  } else {  
    // Step. a <= j
    //   IH: sum(a+1, b+1, f) = sum(a+1, b, f) + f(b+1)
    //    T: sum(a, b+1, f)   = sum(a, b, f)   + f(b+1)
    calc {  
         sumr(a, b+1, f);
      == { reveal sumr(); } 
         f(a) + sumr(a+1, b+1, f);
      == { lem_sumr_dropLast(a+1, b, f); }  // by IH
         f(a) + (sumr(a+1, b, f) + f(b+1));
      == (f(a) + sumr(a+1, b, f)) + f(b+1);
      == { reveal sumr(); }
         sumr(a, b, f) + f(b+1);           
    }
  }
} 

lemma lem_sumr_dropLastAll(a:int, b:int)
  requires a <= b+1
  ensures  forall f:int->real :: sumr(a, b+1, f) == sumr(a, b, f) + f(b+1) 
{ 
  forall f:int->real
    ensures sumr(a, b+1, f) == sumr(a, b, f) + f(b+1) 
  {
     lem_sumr_dropLast(a, b, f);
  }
}

// i <= j+1 ==> c*sum_{k=i}^{j}f(k) = sum_{k=i}^{j}c*f(k)
lemma lem_sumr_linearityConst(a:int, b:int, c:real, f:int->real)
  requires a <= b+1
  ensures  c*sumr(a, b, f) == sumr(a, b, k => c*f(k))
  decreases b - a
{ 
  if a == b+1 {   
    // BC: a > b
    calc {
         c*sumr(b+1, b, f);
      == { reveal sumr(); }
         0.0;
      == { reveal sumr(); }
         sumr(b+1, b, k => c*f(k));       
    }
  } else {  
    // Step. a <= b
    //   IH: c*sum(a+1, b, f) = c*sum(a+1, b, k => c*f(k))
    //    T: c*sum(a, b, f)   = c*sum(a, b, k => f(k))
    calc {  
         c*sumr(a, b, f);
      == { reveal sumr(); } 
         c*(f(a) + sumr(a+1, b, f));
      == c*f(a) + c*sumr(a+1, b, f);         
      == { lem_sumr_linearityConst(a+1, b, c, f); }  // by IH
         c*f(a) + sumr(a+1, b, k => c*f(k)); 
      == (k => c*f(k))(a) + sumr(a+1, b, k => c*f(k));
      == { reveal sumr(); } 
         sumr(a, b, k => c*f(k));           
    } 
  }  
}

// a <= b+1 ==> sum_{k=a}^{b}c = c*(b - a + 1)
lemma lem_sumr_const(a:int, b:int, c:real)
  requires a <= b+1
  ensures  sumr(a, b, k => c) == c * (b - a + 1) as real
  decreases b - a
{ 
  if a == b+1 {   
    // BC: a > b
    calc {
         sumr(b+1, b, k => c); 
      == { reveal sumr(); } 
         0.0; 
      == (b - (b+1) + 1) as real;
    }
  } else {  
    // Step. a <= b
    //   IH: sum(a+1, b, k => c) = c*(b - (a+1) + 1) = c*(b - a)
    //    T: sum(a, b, k => c)   = c*(b - a + 1) 
    calc {  
         sumr(a, b, k => c);
      == { reveal sumr(); }
         c + sumr(a+1, b, x => c);
      == { lem_sumr_const(a+1, b, c); }  // by IH
         (c + c* (b - (a+1) + 1) as real);
      == c + c*((b - a) as real);      
      == c* (b - a + 1) as real;             
    }
  }
}

lemma lem_sumr_constAll(a:int, b:int)
  requires a <= b+1
  ensures  forall c:real :: sumr(a, b, k => c) == c * (b - a + 1) as real
{ 
  forall c:real
    ensures sumr(a, b, k => c) == c * (b - a + 1) as real
  {
     lem_sumr_const(a, b, c);
  }
} 

// a <= b+1 ==> sum_{k=a}^{b}f(k) = sum_{k=a+d}^{b+d}f(k-d)
lemma lem_sumr_shiftIndex(a:int, b:int, d:int, f:int->real)
  requires a <= b+1
  ensures  sumr(a, b, f) == sumr(a+d, b+d, k => f(k-d))
  decreases b - a
{ 
  if a == b+1 {   
    // BC: a > b
    calc {
         sumr(b+1, b, f);
      == { reveal sumr(); }
         0.0;
      == { reveal sumr(); }
         sumr(b+1+d, b+d, k => f(k-d));       
    }
  } else {  
    // Step. a <= b
    //   IH: sum(a+1, b, f) = sum((a+d)+1, b+d, k => f(k-d))
    //    T: sum(a, b, f)   = sum(a+d, b+d, k => f(k-d))
    calc {  
         sumr(a, b, f);
      == { reveal sumr(); } 
         f(a) + sumr(a+1, b, f);
      == { lem_sumr_shiftIndex(a+1, b, d, f); }  // by IH
         f(a) + sumr(a+1+d, b+d, k => f(k-d));
      == (k => f(k-d))(a+d) + sumr((a+d)+1, b+d, k => f(k-d));
      == { reveal sumr(); }
         sumr(a+d, b+d, k => f(k-d));           
    }
  }
} 

// a <= b+1 ==> sum_{k=a}^{b}k = (b*(b+1) + a*(1-a))/2 
lemma lem_sumr_interval(a:int, b:int)
  requires a <= b+1 
  decreases b - a
  ensures sumr(a, b, k => k as real) == (b*(b+1) + a*(1-a)) as real / 2.0
{ 
  if a == b+1 {   
    // BC: a > b
    calc {
         sumr(b+1, b, k => k as real);
      == { reveal sumr(); }
         0.0;
      == (b*(b+1) + ((b+1))*(1-((b+1)))) as real / 2.0;
    }
  } else {  
    // Step. a <= b
    //   IH: sumr(a+1, b, K => k) = (b*(b+1) + (a+1)*(1-(a+1)))/2 
    //    T: sumr(a, b, k => k)   = (b*(b+1) + a*(1-a))/2 
    calc {  
         sumr(a, b, k => k as real);
      == { reveal sumr(); }
         a as real + sumr(a+1, b, k => k as real);
      == { lem_sumr_interval(a+1, b); }  // by IH
         a as real + (b*(b+1) + (a+1)*(1-(a+1))) as real / 2.0;
      == (b*(b+1) + a*(1-a)) as real / 2.0;            
    }
  } 
}

// a <= b+1 /\ (∀ k : a<=k<=b : f(k) == g(k)) 
//          ==> sum_{k=a}^{b}f = sum_{k=a}^{b}g
lemma lem_sumr_leibniz(a:int, b:int, f:int->real, g:int->real)
  requires a <= b+1
  requires forall k:int :: a<=k<=b ==> f(k) == g(k)
  ensures sumr(a, b, f) == sumr(a, b, g)
  decreases b - a
{
  if a == b+1 {   
    // BC: a > b
    calc {
         sumr(b+1, b, f);
      == { reveal sumr(); }
         0.0;
      == { reveal sumr(); }
         sumr(b+1, b, g);       
    }
  } else {  
    // Step. a <= b
    //   IH: sumr(a+1, b, f) = sumr(a+1, b, g)
    //    T: sumr(a, b, f)   = sumr(a, b, g)
    calc {  
         sumr(a, b, f);
      == { reveal sumr(); } 
         f(a) + sumr(a+1, b, f);
      == g(a) + sumr(a+1, b, f);
      == { lem_sumr_leibniz(a+1, b, f, g); }  // by IH
         g(a) + sumr(a+1, b, g);
      == { reveal sumr(); }
         sumr(a, b, g);           
    }
  }
} 

/**************************************************************************
  A special version of Sum on integer codomain
**************************************************************************/
 
// sum_{k=a}^{b}f(k)
opaque ghost function sum(a:int, b:int, f:int->int) : int
  decreases b - a
{
  if a > b  
  then 0
  else f(a) + sum(a+1, b, f)
}

lemma lem_sum_liftEq(a:int, b:int, f:int->int)
  requires a <= b+1
  ensures  sumr(a, b, liftCi2r(f)) == sum(a, b, f) as real
  decreases b - a
{
  reveal sum(), sumr();
}  

// a <= b+1 ==> sum_{k=a}^{b+1}f(k) = sum_{k=a}^{b}f(k) + f(b+1)
lemma lem_sum_dropLast(a:int, b:int, f:int->int)
  requires a <= b+1
  ensures  sum(a, b+1, f) == sum(a, b, f) + f(b+1) 
{ 
  var fr := liftCi2r(f);
  lem_sumr_dropLast(a, b, fr);
  assert sumr(a, b+1, fr) == sumr(a, b, fr) + fr(b+1);
  lem_sum_liftEq(a, b+1, f);
  lem_sum_liftEq(a, b, f);
}

lemma lem_sum_dropLastAll(a:int, b:int)
  requires a <= b+1
  ensures  forall f:int->int :: sum(a, b+1, f) == sum(a, b, f) + f(b+1) 
{ 
  forall f:int->int
    ensures sum(a, b+1, f) == sum(a, b, f) + f(b+1) 
  {
     lem_sum_dropLast(a, b, f);
  }
}

// a <= b+1 ==> sum_{k=a}^{b}c = c*(b - a + 1)
lemma lem_sum_const(a:int, b:int, c:int)
  requires a <= b+1
  ensures  sum(a, b, k => c) == c*(b - a + 1)
{ 
  var fr := liftCi2r(k => c);
  var c' := c as real;
  assert c' == c as real;
  lem_sumr_const(a, b, c');
  assert sumr(a, b, k => c') == (c*(b - a + 1)) as real;
  lem_sum_liftEq(a, b, k => c);
  assert sumr(a, b, fr) == sum(a, b, k => c) as real;
  assert sumr(a, b, fr) == sumr(a, b, k => c')
   by { assert forall k:int :: a<=k<=b ==> c as real == c';
        lem_sumr_leibniz(a, b, fr, k => c'); } 
} 

lemma lem_sum_constAll(a:int, b:int)
  requires a <= b+1
  ensures forall c:int :: sum(a, b, k => c) == (c*(b - a + 1))
{ 
  forall c:int
    ensures sum(a, b, k => c) == (c*(b - a + 1))
  {
     lem_sum_const(a, b, c);
  }
} 

// a <= b+1 /\ (∀ k : a<=k<=b : f(k) == g(k)) 
//          ==> sum_{k=a}^{b}f = sum_{k=a}^{b}g
lemma lem_sum_leibniz(a:int, b:int, f:int->int, g:int->int)
  requires a <= b+1
  requires forall k:int :: a<=k<=b ==> f(k) == g(k)
  ensures  sum(a, b, f) == sum(a, b, g)
{
  var fr := liftCi2r(f);
  var gr := liftCi2r(g);
  lem_sumr_leibniz(a, b, fr, gr);
  assert sumr(a, b, fr) == sumr(a, b, gr);
  lem_sum_liftEq(a, b, f);
  lem_sum_liftEq(a, b, g);
}

// a <= b+1 ==> sum_{k=a}^{b}k = (b*(b+1) + a*(1-a))/2 
lemma lem_sum_interval(a:int, b:int)
  requires a <= b+1 
  decreases b - a
  ensures sum(a, b, k => k) == (b*(b+1) + a*(1-a))/2
{ 
  if a == b+1 {   
    // BC: a > b
    calc {
         sum(b+1, b, k => k);
      == { reveal sum(); }
         0;
      == (b*(b+1) + ((b+1))*(1-((b+1))))/2;
    }
  } else {  
    // Step. a <= b
    //   IH: sum(a+1, b, K => k) = (b*(b+1) + (a+1)*(1-(a+1)))/2 
    //    T: sum(a, b, k => k)   = (b*(b+1) + a*(1-a))/2 
    calc {  
         sum(a, b, k => k);
      == { reveal sum(); }
         a + sum(a+1, b, k => k);
      == { lem_sum_interval(a+1, b); }  // by IH
         a + (b*(b+1) + (a+1)*(1-(a+1)))/2;
      == (b*(b+1) + a*(1-a))/2;            
    }
  }
}

// Following sum lemmas are only stated for integer sum

// sum_{k=1}^{n}k = (n*(n+1))/2 
lemma lem_sum_triangle(n:nat)
  ensures sum(1, n, k => k) == (n*(n+1))/2
{
  lem_sum_interval(1, n);
}

// a <= b+1 ==> sum_{k=a}^{b}(b-k+a) = sum_{k=a}^{b}k
lemma {:axiom} lem_sum_revIndex(a:int, b:int)
  requires a <= b+1
  ensures  sum(a, b, k => b-k+a) == sum(a, b, k => k)


/**************************************************************************
  Sum over sequences
**************************************************************************/

opaque ghost function sumSeq(s:seq<int>, f:int->real): real
  decreases s
{
  if |s| == 0 
  then 0.0
  else f(s[0]) + sumSeq(s[1..], f)
}

/**************************************************************************
  Sum over sets
**************************************************************************/

opaque ghost function sumSet(s:set<int>, f:int->real): real
  decreases s
{
  if |s| == 0 
  then 0.0
  else var x :| x in s;
       f(x) + sumSet(s - {x}, f)
}