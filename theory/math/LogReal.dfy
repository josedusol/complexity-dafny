include "./ExpReal.dfy"
include "./LemFunction.dfy"

/******************************************************************************
  Logarithm over reals
******************************************************************************/

module LogReal {

  import opened ExpReal
  import opened LemFunction

  // log_b(x)
  // We assert lem_log_NonNegative as post for convenience
  ghost function {:axiom} log(b:real, x:real) : real
    requires b > 1.0 && x > 0.0
    ensures  b > 1.0 && x >= 1.0 ==> log(b, x) >= 0.0

  // log_b(1) == 0
  lemma {:axiom} lem_log_One(b:real)
    requires b > 1.0
    ensures  log(b, 1.0) == 0.0

  // b > 1 ∧ x >= 1 ==> log_b(x) >= 0
  lemma {:axiom} lem_log_NonNegative(b:real, x:real)
    requires b > 1.0 && x >= 1.0 
    ensures  log(b, x) >= 0.0 

  // log_b(b) == 1.0
  lemma lem_log_Base(b:real)
    requires b > 1.0
    ensures  log(b, b) == 1.0    
  {
    calc {
           true;
      <==> { lem_exp_One(b); }
           exp(b, 1.0) == b;
      ==>  log(b, exp(b, 1.0)) == log(b, b);
      <==> { lem_logExp_Inverse(b, 1.0); }
           1.0 == log(b, b);
    }
  }
  
  // 1 < b <= x ==> log(b, x) >= 1
  lemma lem_logGEQone(b:real, x:real)
    requires 1.0 < b <= x
    ensures  log(b, x) >= 1.0
  {
    calc {
           b <= x;
      ==>  { lem_log_MonoIncrIFF(b, b, x); }
           log(b, x) >= log(b, b); 
      <==> { lem_log_Base(b); }
           log(b, x) >= 1.0;
    }
  }  

  /******************************************************************************
    log_b(x) and b^x are inverses of each other for x ∈ (0,∞) and b > 1
  ******************************************************************************/

  // log_b(b^x) = x 
  lemma {:axiom} lem_logExp_Inverse(b:real, x:real)
    requires b > 1.0
    requires exp(b, x) > 0.0
    ensures  log(b, exp(b, x)) == x 

  // b^(log_b(x)) = x 
  lemma {:axiom} lem_expLog_Inverse(b:real, x:real)
    requires b > 1.0 && x > 0.0
    ensures  exp(b, log(b, x)) == x

  /******************************************************************************
    Order properties on the argument
  ******************************************************************************/
  
  // For base b > 1, log_b(x) is strictly increasing on argument x ∈ (0,∞)
  // b > 1 ∧ x,y > 0 ∧ x < y ==> log_b(x) < log_b(y)
  lemma {:axiom} lem_log_StrictIncr(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 
    ensures  x < y ==> log(b, x) < log(b, y)

  lemma lem_log_StrictIncrAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x > 0.0 && x < y ==> log(b, x) < log(b, y)
  {
    forall b:real, x:real, y:real | b > 1.0 && x > 0.0
      ensures x < y ==> log(b, x) < log(b, y)
    {
      lem_log_StrictIncr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // b > 1 ∧ x,y > 0 ∧ log_b(x) < log_b(y) ==> x < y
  lemma lem_log_StrictIncrRev(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 && y > 0.0
    ensures  log(b, x) < log(b, y) ==> x < y
  {
    var log_b:real->real := (x => if x > 0.0 then log(b, x) else 0.0);
    assert forall x,y :: x > 0.0 && y > 0.0 ==> (x < y ==> log_b(x) < log_b(y))
      by { lem_log_StrictIncrAuto(); }
    lem_fun_StrictIncrIMPinjectivePred(log_b, (x => x > 0.0));
    assert forall x,y :: x > 0.0 && y > 0.0 ==> (log_b(x) < log_b(y) ==> x < y);
    assert forall x :: x > 0.0 ==> log_b(x) == log(b, x);    
  }

  lemma lem_log_StrictIncrRevAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x > 0.0 && y > 0.0 && log(b, x) < log(b, y) ==> x < y
  {
    forall b:real, x:real, y:real | b > 1.0 && x > 0.0 && y > 0.0
      ensures log(b, x) < log(b, y) ==> x < y
    {
      lem_log_StrictIncrRev(b, x, y);
    }       
  }

  // Join previous facts into an equivalence
  // b > 1 ∧ x,y > 0 ==> (x < y <==> log_b(x) < log_b(y))
  lemma lem_log_StrictIncrIFF(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 && y > 0.0
    ensures  x < y <==> (log(b, x) < log(b, y))
  { 
    lem_log_StrictIncr(b,x,y);
    lem_log_StrictIncrRev(b,x,y);
  }  

  lemma lem_log_StrictIncrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x > 0.0 && y > 0.0 ==> (x < y <==> log(b, x) < log(b, y))
  {
    forall b:real, x:real, y:real | b > 1.0 && x > 0.0 && y > 0.0
      ensures x < y <==> log(b, x) < log(b, y)
    {
      lem_log_StrictIncrIFF(b, x, y);
    }       
  }

  // Weak version of lem_log_StrictIncrIFF
  // b > 1 ∧ x,y > 0 ==> (x <= y <==> log_b(x) <= log_b(y))
  lemma lem_log_MonoIncrIFF(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 && y > 0.0
    ensures  x <= y <==> (log(b, x) <= log(b, y))
  { 
    lem_log_StrictIncrIFFAuto();
  }

  lemma lem_log_MonoIncrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x > 0.0 && y > 0.0 ==> (x <= y <==> log(b, x) <= log(b, y))
  {
    forall b:real, x:real, y:real | b > 1.0 && x > 0.0 && y > 0.0
      ensures x <= y <==> log(b, x) <= log(b, y)
    {
      lem_log_MonoIncrIFF(b, x, y);
    }       
  }  

  /******************************************************************************
    Order properties on the base
  ******************************************************************************/

  // When x ∈ (1,∞), log_b(x) is strictly decreasing on b
  // b1, b2 > 1 ∧ x > 1 ∧ b1 < b2 ==> log_b1(x) > log_b2(x)
  lemma {:axiom} lem_log_BaseStrictDecr(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x > 1.0
    ensures  b1 < b2 ==> log(b1, x) > log(b2, x)     

  lemma lem_log_BaseStrictDecrAuto()
    ensures forall b1:real, b2:real, x:real :: 
      b1 > 1.0 && b2 > 1.0 && x > 1.0 && b1 < b2 ==> log(b1, x) > log(b2, x)   
  {
    forall b1:real, b2:real, x:real | b1 > 1.0 && b2 > 1.0 && x > 1.0
      ensures b1 < b2 ==> log(b1, x) > log(b2, x)  
    {
      lem_log_BaseStrictDecr(b1, b2, x);
    }       
  }

  // Previous fact is reversible
  // b1, b2 > 1 ∧ x > 1 ∧ log_b1(x) > log_b2(x) ==> b1 < b2
  lemma lem_log_BaseStrictDecrRev(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x > 1.0
    ensures  log(b1, x) > log(b2, x) ==> b1 < b2
  {
    var log_x:real->real := (b => if b > 1.0 then log(b, x) else 0.0);
    assert forall b1,b2 :: b1 > 1.0 && b2 > 1.0 ==> (b1 < b2 ==> log_x(b1) > log_x(b2))
      by { lem_log_BaseStrictDecrAuto(); }
    lem_fun_StrictDecrIMPinjectivePred(log_x, (b => b > 1.0));
    assert forall b1,b2 :: b1 > 1.0 && b2 > 1.0 ==> (log_x(b1) > log_x(b2) ==> b1 < b2);
    assert forall b :: b > 1.0 ==> log_x(b) == log(b, x);       
  } 

  lemma lem_log_BaseStrictDecrRevAuto()
    ensures forall b1:real, b2:real, x:real :: 
      b1 > 1.0 && b2 > 1.0 && x > 1.0 && log(b1, x) > log(b2, x) ==> b1 < b2  
  {
    forall b1:real, b2:real, x:real | b1 > 1.0 && b2 > 1.0 && x > 1.0
      ensures log(b1, x) > log(b2, x) ==> b1 < b2 
    {
      lem_log_BaseStrictDecrRev(b1, b2, x);
    }       
  }

  // Join previous facts into an equivalence
  // b1, b2 > 1 ∧ x > 1 ==> (b1 < b2 <==> log_b1(x) > log_b2(x))
  lemma lem_log_BaseStrictDecrIFF(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x > 1.0
    ensures  b1 < b2 <==> log(b1, x) > log(b2, x)
  { 
    lem_log_BaseStrictDecr(b1, b2, x);
    lem_log_BaseStrictDecrRev(b1, b2, x);
  }

  lemma lem_log_BaseStrictDecrIFFAuto()
    ensures forall b1:real, b2:real, x:real :: 
      b1 > 1.0 && b2 > 1.0 && x > 1.0 ==> (b1 < b2 <==> log(b1, x) > log(b2, x))   
  {
    forall b1:real, b2:real, x:real | b1 > 1.0 && b2 > 1.0 && x > 1.0
      ensures b1 < b2 <==> log(b1, x) > log(b2, x)  
    {
      lem_log_BaseStrictDecrIFF(b1, b2, x);
    }       
  }

  // Weak version of lem_log_BaseStrictDecrIFF
  // b1, b2 > 1 ∧ x > 1 ==> (b1 <= b2 <==> log_b1(x) >= log_b2(x))
  lemma lem_log_BaseMonoDecrIFF(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x > 1.0
    ensures  b1 <= b2 <==> log(b1, x) >= log(b2, x)  
  {
    lem_log_BaseStrictDecrIFFAuto();
  }  

  lemma lem_log_BaseMonoDecrIFFAuto()
    ensures forall b1:real, b2:real, x:real :: 
      b1 > 1.0 && b2 > 1.0 && x > 1.0 ==> (b1 <= b2 <==> log(b1, x) >= log(b2, x))   
  {
    forall b1:real, b2:real, x:real | b1 > 1.0 && b2 > 1.0 && x > 1.0
      ensures b1 <= b2 <==> log(b1, x) >= log(b2, x)  
    {
      lem_log_BaseMonoDecrIFF(b1, b2, x);
    }       
  }

  // Weak version of lem_log_BaseStrictDecr, but also holds when x=1
  // b1, b2 > 1 ∧ x >= 1 ∧ b1 <= b2 ==> log_b1(x) >= log_b2(x)
  lemma lem_log_BaseMonoDecr(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x >= 1.0
    ensures  b1 <= b2 ==> log(b1, x) >= log(b2, x)  
  {
    if x == 1.0 {
      lem_log_One(b1);
      lem_log_One(b2);
    } else if x > 1.0 {
      lem_log_BaseStrictDecr(b1, b2, x);
    }
  }

  lemma lem_log_BaseMonoDecrAuto()
    ensures forall b1:real, b2:real, x:real :: 
      b1 > 1.0 && b2 > 1.0 && x >= 1.0 && b1 <= b2 ==> log(b1, x) >= log(b2, x)   
  {
    forall b1:real, b2:real, x:real | b1 > 1.0 && b2 > 1.0 && x >= 1.0
      ensures b1 <= b2 ==> log(b1, x) >= log(b2, x)  
    {
      lem_log_BaseMonoDecr(b1, b2, x);
    }       
  }

  /******************************************************************************
    Universal closures of lemmas
  ******************************************************************************/

  // b > 1 /\ x >= 1 ==> log_b(x) >= 0
  lemma lem_log_NonNegativeAuto()
    ensures  forall b:real, x:real :: 
             b > 1.0 && x >= 1.0 ==> log(b, x) >= 0.0
  {
    forall b:real, x:real | b > 1.0 && x >= 1.0 
      ensures log(b, x) >= 0.0
    {
      lem_log_NonNegative(b, x);
    }    
  }

}