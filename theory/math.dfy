
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
      == n;
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

// floor(x) <= x < floor(x)+1
ghost function {:axiom} floor(x:real) : int
  ensures floor(x) as real <= x
  ensures x < (floor(x) as real) + 1.0

// ceil(x)-1 < x <= ceil(x)
ghost function {:axiom} ceil(x:real) : int
  ensures (ceil(x) as real) - 1.0 < x
  ensures x <= ceil(x) as real
// { 
  //-floor(-x)
  // if x == floor(x) as real 
  // then floor(x) 
  // else floor(x) + 1 
// }

lemma {:axiom} lem_ceilxLEQnIFFxLEQn(x:real, n:int)
  ensures ceil(x) <= n <==> x <= n as real


/**************************************************************************
  Non-negative real numbers and related mathematical functions
**************************************************************************/

type R0 = r | r >= 0.0 witness 0.0

ghost function {:axiom} powr(x:real, y:real) : real
  ensures x >= 0.0 && y >= 0.0 ==> powr(x, y) >= 0.0  

lemma {:axiom} lem_powrZeroZero() // assume 0.0^0.0 = 1
  ensures  powr(0.0, 0.0) == 1.0 

lemma {:axiom} lem_powrZero(x:real)
  requires x > 0.0
  ensures  powr(x, 0.0) == 1.0 

lemma {:axiom} lem_powrOne(x:real)
  requires x > 0.0
  ensures  powr(x, 1.0) == x

lemma {:axiom} lem_powrProduct(x:real, y:real, z:real)
  requires x > 0.0 
  ensures powr(x, y+z) == powr(x, y)*powr(x, z)  

lemma {:axiom} lem_powrZeroAll()
  ensures forall x:real :: x > 0.0 ==> powr(x, 0.0) == 1.0 

lemma {:axiom} lem_powrOneAll()
  ensures forall x:real :: x > 0.0 ==> powr(x, 1.0) == x  

lemma {:axiom} lem_powrProductAll()
  ensures forall x:real, y:real, z:real :: 
          x > 0.0 ==> powr(x, y+z) == powr(x, y)*powr(x, z)

lemma lem_powrTwo(x:real) 
  requires x > 0.0
  ensures  powr(x, 2.0) == x*x
{  
  calc {
       powr(x, 2.0);
    == { lem_powrProduct(x, 1.0, 1.0); }
       powr(x, 1.0)*powr(x, 1.0);
    == { lem_powrOne(x); }
       x*x;
  } 
} 

lemma lem_powrTwoAll()
  ensures forall x:real :: x > 0.0 ==> powr(x, 2.0) == x*x
{
  forall x:real | x > 0.0
    ensures powr(x, 2.0) == x*x
  {
    lem_powrTwo(x);
  }
}

lemma lem_powrDef(x:real, y:real)
  requires x > 0.0 
  ensures  x*powr(x, y) == powr(x, y + 1.0)
{ 
  calc {
       x*powr(x, y);
    == { lem_powrOne(x); }
       powr(x, 1.0)*powr(x, y);
    == { lem_powrProduct(x, 1.0, y); }
       powr(x, y + 1.0);
  } 
} 

lemma lem_powrDefAll()
  ensures forall x:real, y:real :: 
          x > 0.0 ==> x*powr(x, y) == powr(x, y + 1.0)
{
  forall x:real, y:real | x > 0.0
    ensures x*powr(x, y) == powr(x, y + 1.0)
  {
    lem_powrDef(x, y);
  }
}

/**************************************************************************
  Function equality
**************************************************************************/

lemma {:axiom} lem_funExt<A,B>(f1:A->B, f2:A->B)
  requires forall x:A :: f1(x) == f2(x)
  ensures f1 == f2

/**************************************************************************
  Maximum and minimum
**************************************************************************/

function max(a:int, b:int) : int
{
  if a < b then b else a
}

function min(a:int, b:int): int
{
  if a < b then a else b
}

// n >= 0 ==> max(0,n) = n
lemma lem_max0n(n:int)
  requires n >= 0
  ensures max(0, n) == n
{}

/**************************************************************************
  Miscelanious stuff
**************************************************************************/

ghost function liftD<T>(f:nat->T, default:T) : int->T
{
  k => if k < 0 then default else f(k as nat)
}

ghost function liftCi2r(f:int->int) : int->real
{
  n => f(n) as real
}

// Lift f:nat->nat to f':nat->R0
ghost function liftToR0(f:nat->nat) : nat->R0
{
  n => f(n) as R0
}

// apparently useless
ghost function ite<T>(cond: bool, thenBranch: T, elseBranch: T) : T
{
  if cond then thenBranch else elseBranch
}