
/**************************************************************************
  Power over non-negative integers
**************************************************************************/

// b^e
opaque ghost function pow(b:nat, e:nat) : nat
  decreases e
{
  if e == 0 then 1 else b*pow(b, e-1)
}

lemma lem_pow2FirstValues()
  ensures pow(2,0) == 1
  ensures pow(2,1) == 2 
  ensures pow(2,2) == 4
  ensures pow(2,3) == 8
  ensures pow(2,4) == 16
{
  reveal pow();
}

// b>1 /\ n <= m ==> b^n <= b^m
lemma lem_powMono(b:nat, n:nat, m:nat)
  requires b > 1
  ensures  n <= m ==> pow(b, n) <= pow(b, m)
  decreases n, m
{ 
  reveal pow();
  if n != 0 && m != 0 {  
    lem_powMono(b, n-1, m-1); 
  }
}

// b>0 ==> b^e > 0
lemma lem_powIsPositive(b:nat, e:nat)
  requires b > 0
  ensures pow(b,e) > 0
{
  if e == 0 { 
    // BC: e = 0
    calc {
         pow(b, 0);
      == { reveal pow(); }
         1;
      >  0;  
    }
  } else {
    // Step. n > 0
    //   IH: b^(e-1)  > 0
    //    T:      b^e > 0
    lem_powIsPositive(b, e-1); 
    calc {
         pow(b,e);
      == { reveal pow(); }
         b*pow(b, e-1);
      >  { lem_powIsPositive(b, e-1); }
         0;  
    }
  }
}

lemma {:axiom} lem_pown1(n:nat)
  ensures pow(n,1) == n

lemma lem_pown1All()
  ensures forall n:nat :: pow(n,1) == n  
{ 
  forall n:nat ensures pow(n,1) == n {
    lem_pown1(n);
  }
}

lemma {:axiom} lem_pown2(n:nat)
  ensures pow(n,2) == n*n

lemma lem_pown2All()
  ensures forall n:nat :: pow(n,2) == n*n  
{
  forall n:nat ensures pow(n,2) == n*n {
    lem_pown2(n);
  }
}  

lemma {:axiom} lem_pown3(n:nat)
  ensures pow(n,3) == n*n*n  

lemma lem_pown3All()
  ensures forall n:nat :: pow(n,3) == n*n*n 
{
  forall n:nat ensures pow(n,3) == n*n*n {
    lem_pown3(n);
  }
}   

lemma {:axiom} lem_binomial2(n:nat)
  ensures pow(n+1,2) == n*n + 2*n + 1

lemma {:axiom} lem_binomial(n:nat)
  requires n > 0
  ensures pow(n,2) == pow(n-1,2) + 2*(n-1) + 1 

/**************************************************************************
  Base 2 logarithm over non-negative integers
**************************************************************************/

// log2(n) 
opaque ghost function log2(n:nat) : nat
  requires  n > 0
  decreases n
{
  if n == 1 then 0 else 1 + log2(n/2)
}

lemma lem_log2FirstValues()
  ensures log2(1) == 0
  ensures log2(2) == 1
  ensures log2(3) == 1
  ensures log2(4) == 2
  ensures log2(5) == 2
{
  reveal log2();
}

// n>0 /\ m>0 /\ n <= m ==> log2(n) <= log2(m)
lemma lem_log2Mono(n:nat, m:nat)
  requires n > 0 && m > 0
  ensures  n <= m ==> log2(n) <= log2(m)
  decreases n, m
{
  reveal log2();
  if n != 1 && m != 1 { 
    lem_log2Mono(n-1, m-1); 
  }
}

/**************************************************************************
  log2(n) and 2^n are inverses of each other
  However, this holds only in a restricted sense because log2(n) is 
  in fact floor(log2(n)).
  So, in one direction we have the equality
    log2(2^n) == n 
  but in the other we only have the inequality
    2^log2(n) <= n
  unless n is an exact power of 2.
**************************************************************************/

// log2(2^n) = n 
lemma lem_log2AndPow2Inverse(n:nat)
  requires pow(2,n) > 0
  ensures  log2(pow(2,n)) == n 
{
  if n == 0 {
    // BC: n = 0
    calc {
         log2(pow(2,0));
      == { lem_pow2FirstValues(); }
         log2(1);
      == { lem_log2FirstValues(); }
         0;   
    }
  } else {
    // Step. n > 1
    //   IH: log2(2^(n-1)) = n-1 
    //    T: log2(2^n)     = n 
    calc {
      log2(pow(2, n));
      == { reveal pow(); }
      log2(2*pow(2, n-1));
      == { reveal log2(); }
      1 + log2(pow(2, n-1));
      == { lem_log2AndPow2Inverse(n-1); } // IH
      1 + (n - 1);
      == 
      n;
    }
  }
}

// If n=2^k then log2(2^n)=n 
lemma {:axiom} lem_Pow2Andlog2Inverse(n:nat, k:nat)
  requires pow(2, k) > 0
  requires n == pow(2, k) 
  ensures pow(2, log2(n)) == n

/**************************************************************************
  Square root over non-negative integers
**************************************************************************/

// sqrt(n)
opaque ghost function sqrt(n:nat) : nat
  decreases n
{
  if n == 0 then 0
  else var r := sqrt(n-1); 
       if (r+1)*(r+1) <= n
       then r + 1
       else r
}

/**************************************************************************
  Factorial
**************************************************************************/

// !n
opaque ghost function fac(n:nat) : nat
  decreases n
{
  if n == 0 then 1 else n*fac(n-1)
}

/**************************************************************************
  Floors and ceilings
**************************************************************************/

// lemma {:axiom} floorDiv(a:int, b:int)
//   requires a >= 0 && b > 0
//   ensures exists x :: x <= a/b < x + 1

// floor(x) <= x < floor(x)+1
ghost function {:axiom} floor(x:real) : int
  ensures floor(x) as real <= x
  ensures x < (floor(x) as real) + 1.0

// ceil(x)-1 <= x < ceil(x)
ghost function {:axiom} ceil(x:real) : int
  ensures (ceil(x) as real) - 1.0 <= x
  ensures x < ceil(x) as real
// { 
  //-floor(-x)
  // if x == floor(x) as real 
  // then floor(x) 
  // else floor(x) + 1 
// }

/**************************************************************************
  Non-negative real numbers and related mathematical functions
**************************************************************************/

type R0 = r | r >= 0.0 witness 0.0

ghost function powr0(x:R0, y:R0) : R0

lemma {:axiom} lem_powrZero(x:R0)
  requires x > 0.0
  ensures  powr0(x, 0.0) == 1.0 

lemma {:axiom} lem_powrOne(x:R0)
  requires x > 0.0
  ensures  powr0(x, 1.0) == x

lemma {:axiom} lem_powrProduct(x:R0, y:R0, z:R0)
  requires x > 0.0 
  ensures powr0(x, y+z) == powr0(x, y)*powr0(x, z)  

lemma {:axiom} lem_powrZeroAll()
  ensures forall x:R0 :: x > 0.0 ==> powr0(x, 0.0) == 1.0 

lemma {:axiom} lem_powrOneAll()
  ensures forall x:R0 :: x > 0.0 ==> powr0(x, 1.0) == x  

lemma {:axiom} lem_powrProductAll()
  ensures forall x:R0, y:R0, z:R0 :: x > 0.0 ==> powr0(x, y+z) == powr0(x, y)*powr0(x, z)

lemma lem_powrTwo(x:R0) 
  requires x > 0.0
  ensures powr0(x, 2.0) == x*x
{  
  assert powr0(x, 2.0) == powr0(x, 1.0 + 1.0);
  lem_powrProduct(x, 1.0, 1.0);
  lem_powrOne(x);
} 

/**************************************************************************
  Function equality
**************************************************************************/

lemma {:axiom} lem_funExt<A,B>(f1:A->B, f2:A->B)
  requires forall x:A :: f1(x) == f2(x)
  ensures f1 == f2

/**************************************************************************
  Sum over intervals
**************************************************************************/

// sum_{k=i}^{j}f(k)
opaque ghost function sum(i:nat, j:nat, f:nat->nat): nat
  decreases j - i
{
  if i > j  
  then 0 
  else f(i) + sum(i+1 , j, f)
}

// i <= j+1 ==>   sum_{k=i}^{j}ITE(i<=k<=j,f(k),0) 
//              = f(i) + sum_{k=i+1}^{j}ITE(i+1<=k<=j,f(k),0)
lemma {:axiom} lem_sumGuardedDropFirst(i:nat, j:nat, f:nat->nat)
  requires i <= j+1
  ensures    sum(i, j, k => if i<=k<=j then f(k) else 0) 
          ==   (if i<=i<=j then f(i) else 0) 
             + sum(i+1, j, k => if i+1<=k<=j then f(k) else 0) 

lemma {:axiom} lem_sumGuardedShiftLowerBound(i:nat, j:nat, f:nat->nat)
  //requires i+1 <= j
  ensures    sum(i+1, j, k => if i+1<=k<=j then f(k) else 0) 
          == sum(i+1, j, k => if i<=k<=j then f(k) else 0) 

// i <= j+1 ==> sum_{k=i}^{j+1}f(k) = sum_{k=i}^{j}f(k) + f(j+1)
lemma lem_sumDropLast(i:nat, j:nat, f:nat->nat)
  requires i <= j+1
  decreases j - i
  ensures sum(i, j+1, f) == sum(i, j, f) + f(j+1) 
{ 
  if i == j+1 {   
    // BC: i > j
    calc {
         sum(j+1, j+1, f);
      == { reveal sum(); }
         f(j+1);
      == 
         0 + f(j+1) ;
      == { reveal sum(); }
         sum(i, j, f) + f(j+1) ;       
    }
  } else {  
    // Step. i <= j
    //   IH: sum(i+1, j+1, f) = sum(i+1, j, f) + f(j+1)
    //    T: sum(i, j+1, f)   = sum(i, j, f)   + f(j+1)
    calc {  
         sum(i, j+1, f);
      == { reveal sum(); } 
         f(i) + sum(i+1, j+1, f);
      == { lem_sumDropLast(i+1, j, f); }  // by IH
         f(i) + (sum(i+1, j, f) + f(j+1));
      == 
         (f(i) + sum(i+1, j, f)) + f(j+1);
      == { reveal sum(); }
         sum(i, j, f) + f(j+1);           
    }
  }
} 

lemma lem_sumDropLastAll(i:nat, j:nat)
  requires i <= j+1
  ensures forall f:nat->nat :: sum(i, j+1, f) == sum(i, j, f) + f(j+1) 
{ 
  forall f:nat->nat
    ensures sum(i, j+1, f) == sum(i, j, f) + f(j+1) 
  {
     lem_sumDropLast(i, j, f);
  }
} 

// i <= j+1 ==> sum_{k=i}^{j}c = c*(j - i + 1)
lemma lem_sumOverConst(i:nat, j:nat, c:nat)
  requires i <= j+1
  decreases j - i
  ensures sum(i, j, k => c) == c*(j - i + 1)
{ 
  if i == j+1 {   
    // BC: i > j
    calc {
         sum(j+1, j, k => c);
      == { reveal sum(); }
         0;
      == 
         j - (j+1) + 1;
    }
  } else {  
    // Step. i <= j
    //   IH: sum(i+1, j, k => c) = c*(j -(i+1) + 1) = c*(j - i)
    //    T: sum(i, j, k => c)   = c*(j -i + 1) 
    calc {  
         sum(i, j, k => c);
      == { reveal sum(); }
         c + sum(i+1, j, x => c);
      == { lem_sumOverConst(i+1, j, c); }  // by IH
         c + c*(j -(i+1) + 1);
      == 
         c + c*(j - i);      
      == 
         c*(j -i + 1);             
    }
  }
}

lemma lem_sumOverConstAll(i:nat, j:nat)
  requires i <= j+1
  ensures forall c:nat :: sum(i, j, x => c) == c*(j - i + 1)
{ 
  forall c:nat
    ensures sum(i, j, x => c) == c*(j - i + 1)
  {
     lem_sumOverConst(i, j, c);
  }
} 

// i <= j+1 ==> sum_{k=i}^{j}k = (j*(j+1) + i*(1-i))/2 
lemma lem_sumInterval(i:nat, j:nat)
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
      == 
         (j*(j+1) + ((j+1))*(1-((j+1))))/2;
    }
  } else {  
    // Step. i <= j
    //   IH: sum(i+1, j, K => k) = (j*(j+1) + (i+1)*(1-(i+1)))/2 
    //    T: sum(i, j, k => k)   = (j*(j+1) + i*(1-i))/2 
    calc {  
         sum(i, j, k => k);
      == { reveal sum(); }
         i + sum(i+1, j, k => k);
      == { lem_sumInterval(i+1, j); }  // by IH
         i + (j*(j+1) + (i+1)*(1-(i+1)))/2 ;
      == 
         (j*(j+1) + i*(1-i))/2;            
    }
  }
}

// sum_{k=1}^{n}k = (n*(n+1))/2 
lemma lem_sumGauss(n:nat)
  ensures sum(1, n, k => k) == (n*(n+1))/2 
{
   lem_sumInterval(1, n);
}

// i <= j+1 /\ (∀ k : i<=k<=j : f(k) == g(k)) 
//          ==> sum_{k=i}^{j}f = sum_{k=i}^{j}g
lemma {:axiom} lem_sumLeibniz(i:nat, j:nat, f:nat->nat, g:nat->nat)
  requires i <= j+1
  requires forall k:nat :: i<=k<=j ==> f(k) == g(k)
  ensures sum(i, j, f) == sum(i, j, g)

// i <= j+1 ==> sum_{k=i}^{j}(j-k+i) = sum_{k=i}^{j}k
lemma {:axiom} lem_sumReverseIndex(i:nat, j:nat)
  requires i <= j+1
  ensures sum(i, j, k => if i<=k<=j then j-k+i else 0) == sum(i, j, k => k)


/**************************************************************************
  Sum over sequences
**************************************************************************/

ghost function sumSeq(s:seq<nat>, f:nat->nat): nat
  decreases s
{
  if |s| == 0 
  then 0
  else f(s[0]) + sumSeq(s[1..], f)
}

/**************************************************************************
  Sum over sets
**************************************************************************/

ghost function sumSet(s:set<nat>, f:nat->nat): nat
  decreases s
{
  if |s| == 0 
  then 0
  else var x :| x in s;
       f(x) + sumSet(s - {x}, f)
}

/**************************************************************************
  Miscelanious stuff
**************************************************************************/

// no sirve pa un carajo
ghost function ite<T>(cond: bool, thenBranch: T, elseBranch: T) : T
{
  if cond then thenBranch else elseBranch
}