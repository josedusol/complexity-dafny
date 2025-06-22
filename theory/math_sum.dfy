include "./math.dfy"

/**************************************************************************
  Sum over integer intervals
**************************************************************************/

// sum_{k=i}^{j}f(k)
opaque ghost function sumr(i:int, j:int, f:int->real): real
  decreases j - i
{
  if i > j  
  then 0.0
  else f(i) + sumr(i+1 , j, f)
}

// i <= j+1 ==> sum_{k=i}^{j+1}f(k) = sum_{k=i}^{j}f(k) + f(j+1)
lemma lem_sumr_dropLast(i:int, j:int, f:int->real)
  requires i <= j+1
  ensures  sumr(i, j+1, f) == sumr(i, j, f) + f(j+1) 
  decreases j - i
{ 
  if i == j+1 {   
    // BC: i > j
    calc {
         sumr(j+1, j+1, f);
      == { reveal sumr(); }
         f(j+1);
      == 0.0 + f(j+1) ;
      == { reveal sumr(); }
         sumr(i, j, f) + f(j+1) ;       
    }
  } else {  
    // Step. i <= j
    //   IH: sum(i+1, j+1, f) = sum(i+1, j, f) + f(j+1)
    //    T: sum(i, j+1, f)   = sum(i, j, f)   + f(j+1)
    calc {  
         sumr(i, j+1, f);
      == { reveal sumr(); } 
         f(i) + sumr(i+1, j+1, f);
      == { lem_sumr_dropLast(i+1, j, f); }  // by IH
         f(i) + (sumr(i+1, j, f) + f(j+1));
      == (f(i) + sumr(i+1, j, f)) + f(j+1);
      == { reveal sumr(); }
         sumr(i, j, f) + f(j+1);           
    }
  }
} 

lemma lem_sumr_dropLastAll(i:int, j:int)
  requires i <= j+1
  ensures  forall f:int->real :: sumr(i, j+1, f) == sumr(i, j, f) + f(j+1) 
{ 
  forall f:int->real
    ensures sumr(i, j+1, f) == sumr(i, j, f) + f(j+1) 
  {
     lem_sumr_dropLast(i, j, f);
  }
}

// i <= j+1 ==> c*sum_{k=i}^{j}f(k) = sum_{k=i}^{j}c*f(k)
lemma lem_sumr_linearityConst(i:int, j:int, c:real, f:int->real)
  requires i <= j+1
  ensures  c*sumr(i, j, f) == sumr(i, j, k => c*f(k))
  decreases j - i
{ 
  if i == j+1 {   
    // BC: i > j
    calc {
         c*sumr(j+1, j, f);
      == { reveal sumr(); }
         0.0;
      == { reveal sumr(); }
         sumr(j+1, j, k => c*f(k));       
    }
  } else {  
    // Step. i <= j
    //   IH: c*sum(i+1, j, f) = c*sum(i+1, j, k => c*f(k))
    //    T: c*sum(i, j, f)   = c*sum(i, j, k => f(k))
    calc {  
         c*sumr(i, j, f);
      == { reveal sumr(); } 
         c*(f(i) + sumr(i+1, j, f));
      == c*f(i) + c*sumr(i+1, j, f);         
      == { lem_sumr_linearityConst(i+1, j, c, f); }  // by IH
         c*f(i) + sumr(i+1, j, k => c*f(k)); 
      == (k => c*f(k))(i) + sumr(i+1, j, k => c*f(k));
      == { reveal sumr(); } 
         sumr(i, j, k => c*f(k));           
    } 
  }  
}


// i <= j+1 ==> sum_{k=i}^{j}c = c*(j - i + 1)
lemma lem_sumr_const(i:int, j:int, c:real)
  requires i <= j+1
  ensures  sumr(i, j, k => c) == c * (j - i + 1) as real
  decreases j - i
{ 
  if i == j+1 {   
    // BC: i > j
    calc {
         sumr(j+1, j, k => c); 
      == { reveal sumr(); } 
         0.0; 
      == (j - (j+1) + 1) as real;
    }
  } else {  
    // Step. i <= j
    //   IH: sum(i+1, j, k => c) = c*(j -(i+1) + 1) = c*(j - i)
    //    T: sum(i, j, k => c)   = c*(j -i + 1) 
    calc {  
         sumr(i, j, k => c);
      == { reveal sumr(); }
         c + sumr(i+1, j, x => c);
      == { lem_sumr_const(i+1, j, c); }  // by IH
         (c + c* (j -(i+1) + 1) as real);
      == c + c*((j - i) as real);      
      == c* (j -i + 1) as real;             
    }
  }
}

lemma lem_sumr_constAll(i:int, j:int)
  requires i <= j+1
  ensures  forall c:real :: sumr(i, j, k => c) == c * (j - i + 1) as real
{ 
  forall c:real
    ensures sumr(i, j, k => c) == c * (j - i + 1) as real
  {
     lem_sumr_const(i, j, c);
  }
} 

// i <= j+1 ==> sum_{k=i}^{j}f(k) = sum_{k=i+d}^{j+d}f(k-d)
lemma lem_sumr_shiftIndex(i:int, j:int, d:int, f:int->real)
  requires i <= j+1
  ensures  sumr(i, j, f) == sumr(i+d, j+d, k => f(k-d))
  decreases j - i
{ 
  if i == j+1 {   
    // BC: i > j
    calc {
         sumr(j+1, j, f);
      == { reveal sumr(); }
         0.0;
      == { reveal sumr(); }
         sumr(j+1+d, j+d, k => f(k-d));       
    }
  } else {  
    // Step. i <= j
    //   IH: sum(i+1, j, f) = sum((i+d)+1, j+d, k => f(k-d))
    //    T: sum(i, j, f)   = sum(i+d, j+d, k => f(k-d))
    calc {  
         sumr(i, j, f);
      == { reveal sumr(); } 
         f(i) + sumr(i+1, j, f);
      == { lem_sumr_shiftIndex(i+1, j, d, f); }  // by IH
         f(i) + sumr(i+1+d, j+d, k => f(k-d));
      == (k => f(k-d))(i+d) + sumr((i+d)+1, j+d, k => f(k-d));
      == { reveal sumr(); }
         sumr(i+d, j+d, k => f(k-d));           
    }
  }
} 

// i <= j+1 /\ (∀ k : i<=k<=j : f(k) == g(k)) 
//          ==> sum_{k=i}^{j}f = sum_{k=i}^{j}g
lemma lem_sumr_leibniz(i:int, j:int, f:int->real, g:int->real)
  requires i <= j+1
  requires forall k:int :: i<=k<=j ==> f(k) == g(k)
  ensures sumr(i, j, f) == sumr(i, j, g)
  decreases j - i
{
  if i == j+1 {   
    // BC: i > j
    calc {
         sumr(j+1, j, f);
      == { reveal sumr(); }
         0.0;
      == { reveal sumr(); }
         sumr(j+1, j, g);       
    }
  } else {  
    // Step. i <= j
    //   IH: sumr(i+1, j, f) = sumr(i+1, j, g)
    //    T: sumr(i, j, f)   = sumr(i, j, g)
    calc {  
         sumr(i, j, f);
      == { reveal sumr(); } 
         f(i) + sumr(i+1, j, f);
      == {  } 
         g(i) + sumr(i+1, j, f);
      == { lem_sumr_leibniz(i+1, j, f, g); }  // by IH
         g(i) + sumr(i+1, j, g);
      == { reveal sumr(); }
         sumr(i, j, g);           
    }
  }
} 

/**************************************************************************
  A special version of Sum on integer codomain
**************************************************************************/
 
// sum_{k=i}^{j}f(k)
opaque ghost function sum(i:int, j:int, f:int->int) : int
  decreases j - i
{
  if i > j  
  then 0
  else f(i) + sum(i+1, j, f)
}

lemma lem_sum_liftEq(i:int, j:int, f:int->int)
  requires i <= j+1
  ensures  sumr(i, j, liftCi2r(f)) == sum(i, j, f) as real
  decreases j - i
{
  reveal sum(), sumr();
}  

// i <= j+1 ==> sum_{k=i}^{j+1}f(k) = sum_{k=i}^{j}f(k) + f(j+1)
lemma lem_sum_dropLast(i:int, j:int, f:int->int)
  requires i <= j+1
  ensures  sum(i, j+1, f) == sum(i, j, f) + f(j+1) 
{ 
  var fr := liftCi2r(f);
  lem_sumr_dropLast(i, j, fr);
  assert sumr(i, j+1, fr) == sumr(i, j, fr) + fr(j+1);
  lem_sum_liftEq(i, j+1, f);
  lem_sum_liftEq(i, j, f);
}

lemma lem_sum_dropLastAll(i:int, j:int)
  requires i <= j+1
  ensures  forall f:int->int :: sum(i, j+1, f) == sum(i, j, f) + f(j+1) 
{ 
  forall f:int->int
    ensures sum(i, j+1, f) == sum(i, j, f) + f(j+1) 
  {
     lem_sum_dropLast(i, j, f);
  }
}

// i <= j+1 ==> sum_{k=i}^{j}c = c*(j - i + 1)
lemma lem_sum_const(i:int, j:int, c:int)
  requires i <= j+1
  ensures  sum(i, j, k => c) == c*(j - i + 1)
{ 
  var fr := liftCi2r(k => c);
  var c' := c as real;
  assert c' == c as real;
  lem_sumr_const(i, j, c');
  assert sumr(i, j, k => c') == (c*(j - i + 1)) as real;
  lem_sum_liftEq(i, j, k => c);
  assert sumr(i, j, fr) == sum(i, j, k => c) as real;
  assert sumr(i, j, fr) == sumr(i, j, k => c')
   by { assert forall k:int :: i<=k<=j ==> c as real == c';
        lem_sumr_leibniz(i, j, fr, k => c'); } 
} 

lemma lem_sum_constAll(i:int, j:int)
  requires i <= j+1
  ensures forall c:int :: sum(i, j, k => c) == (c*(j - i + 1))
{ 
  forall c:int
    ensures sum(i, j, k => c) == (c*(j - i + 1))
  {
     lem_sum_const(i, j, c);
  }
} 

// i <= j+1 /\ (∀ k : i<=k<=j : f(k) == g(k)) 
//          ==> sum_{k=i}^{j}f = sum_{k=i}^{j}g
lemma lem_sum_leibniz(i:int, j:int, f:int->int, g:int->int)
  requires i <= j+1
  requires forall k:int :: i<=k<=j ==> f(k) == g(k)
  ensures  sum(i, j, f) == sum(i, j, g)
{
  var fr := liftCi2r(f);
  var gr := liftCi2r(g);
  lem_sumr_leibniz(i, j, fr, gr);
  assert sumr(i, j, fr) == sumr(i, j, gr);
  lem_sum_liftEq(i, j, f);
  lem_sum_liftEq(i, j, g);
}

// Following sum lemmas are only stated for integer sum

// i <= j+1 ==> sum_{k=i}^{j}k = (j*(j+1) + i*(1-i))/2 
lemma lem_sum_interval(i:int, j:int)
  requires i <= j+1 
  decreases j - i
  ensures sum(i, j, k => k) == (j*(j+1) + i*(1-i))/2
{ 
  if i == j+1 {   
    // BC: i > j
    calc {
         sum(j+1, j, k => k);
      == { reveal sum(); }
         0;
      == (j*(j+1) + ((j+1))*(1-((j+1))))/2;
    }
  } else {  
    // Step. i <= j
    //   IH: sum(i+1, j, K => k) = (j*(j+1) + (i+1)*(1-(i+1)))/2 
    //    T: sum(i, j, k => k)   = (j*(j+1) + i*(1-i))/2 
    calc {  
         sum(i, j, k => k);
      == { reveal sum(); }
         i + sum(i+1, j, k => k);
      == { lem_sum_interval(i+1, j); }  // by IH
         i + (j*(j+1) + (i+1)*(1-(i+1)))/2;
      == (j*(j+1) + i*(1-i))/2;            
    }
  }
}

// sum_{k=1}^{n}k = (n*(n+1))/2 
lemma lem_sum_triangle(n:nat)
  ensures sum(1, n, k => k) == (n*(n+1))/2
{
  lem_sum_interval(1, n);
}

// i <= j+1 ==> sum_{k=i}^{j}(j-k+i) = sum_{k=i}^{j}k
lemma {:axiom} lem_sum_revIndex(i:int, j:int)
  requires i <= j+1
  ensures sum(i, j, k => j-k+i) == sum(i, j, k => k)


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