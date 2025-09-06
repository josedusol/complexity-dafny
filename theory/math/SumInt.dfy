include "./LemFunction.dfy"
include "./SumReal.dfy"

/******************************************************************************
  Sum over integer intervals and integer codomain
******************************************************************************/

module SumInt {
  import opened LemFunction  
  import R = SumReal

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
    ensures  R.sum(a, b, liftCi2r(f)) == sum(a, b, f) as real
    decreases b - a
  {
    reveal sum(), R.sum();
  }  

  // a <= b+1 ==> sum_{k=a}^{b+1}f(k) = sum_{k=a}^{b}f(k) + f(b+1)
  lemma lem_sum_dropLast(a:int, b:int, f:int->int)
    requires a <= b+1
    ensures  sum(a, b+1, f) == sum(a, b, f) + f(b+1) 
  { 
    var fr := liftCi2r(f);
    R.lem_sum_dropLast(a, b, fr);
    assert R.sum(a, b+1, fr) == R.sum(a, b, fr) + fr(b+1);
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
    R.lem_sum_const(a, b, c');
    assert R.sum(a, b, k => c') == (c*(b - a + 1)) as real;
    lem_sum_liftEq(a, b, k => c);
    assert R.sum(a, b, fr) == sum(a, b, k => c) as real;
    assert R.sum(a, b, fr) == R.sum(a, b, k => c')
    by { assert forall k:int :: a<=k<=b ==> c as real == c';
         R.lem_sum_leibniz(a, b, fr, k => c'); } 
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

  // a <= b+1 /\ (∀ k : a<=k<=b : f(k) == g(k)) 
  //          ==> sum_{k=a}^{b}f = sum_{k=a}^{b}g
  lemma lem_sum_leibniz(a:int, b:int, f:int->int, g:int->int)
    requires a <= b+1
    requires forall k:int :: a<=k<=b ==> f(k) == g(k)
    ensures  sum(a, b, f) == sum(a, b, g)
  {
    var fr := liftCi2r(f);
    var gr := liftCi2r(g);
    R.lem_sum_leibniz(a, b, fr, gr);
    assert R.sum(a, b, fr) == R.sum(a, b, gr);
    lem_sum_liftEq(a, b, f);
    lem_sum_liftEq(a, b, g);
  }

  // a <= b+1 /\ (∀ k : a<=k<=b : f(k) <= g(k)) 
  //          ==> sum_{k=a}^{b}f <= sum_{k=a}^{b}g
  lemma lem_sum_mono(a:int, b:int, f:int->int, g:int->int)
    requires a <= b+1
    requires forall k:int :: a<=k<=b ==> f(k) <= g(k)
    ensures  sum(a, b, f) <= sum(a, b, g)
  {
    var fr := liftCi2r(f);
    var gr := liftCi2r(g);
    R.lem_sum_mono(a, b, fr, gr);
    assert R.sum(a, b, fr) <= R.sum(a, b, gr);
    lem_sum_liftEq(a, b, f);
    lem_sum_liftEq(a, b, g);
  }

  // a<=j<=b ==> sum_{k=a}^{b}f = sum_{k=a}^{j}f + sum_{k=j+1}^{b}f
  lemma lem_sum_split(a:int, b:int, j:int, f:int->int)
    requires a <= j <= b
    ensures sum(a, b, f) == sum(a, j, f) + sum(j+1, b, f)
  {
    var fr := liftCi2r(f);
    R.lem_sum_split(a, b, j, fr);
    assert R.sum(a, b, fr) == R.sum(a, j, fr) + R.sum(j+1, b, fr);
    lem_sum_liftEq(a, b, f);  
    lem_sum_liftEq(a, j, f);   
    lem_sum_liftEq(j+1, b, f);   
  }

  // a<=j<=b ==> sum_{k=a}^{b}f = sum_{k=a}^{j-1}f + sum_{k=j}^{b}f
  lemma lem_sum_split2(a:int, b:int, j:int, f:int->int)
    requires a <= j <= b
    ensures sum(a, b, f) == sum(a, j-1, f) + sum(j, b, f)
  {
    var fr := liftCi2r(f);
    R.lem_sum_split2(a, b, j, fr);
    assert R.sum(a, b, fr) == R.sum(a, j-1, fr) + R.sum(j, b, fr);
    lem_sum_liftEq(a, b, f);  
    lem_sum_liftEq(a, j-1, f);   
    lem_sum_liftEq(j, b, f);     
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
  
}