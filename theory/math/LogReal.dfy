include "./ExpReal.dfy"
include "./LemFunction.dfy"

/******************************************************************************
  Logarithm over reals
******************************************************************************/

module LogReal {

  import opened ExpReal
  import opened LemFunction

  // There is exactly one y such that b^y = x
  lemma {:axiom} lem_log_ExistsUnique(b:real, x:real)
    requires b > 1.0 && x > 0.0
    ensures  exists y :: exp(b, y) == x
    ensures  forall z1, z2 :: exp(b, z1) == x && exp(b, z2) == x ==> z1 == z2
    // Proof.
    // Existence by intermediate value theorem
    // Uniquenes by injectivity implied by strictly increasing growth

  // log_b(x) = the unique y such that exp(b,y) = x
  opaque ghost function log(b:real, x:real) : real
    requires b > 1.0 && x > 0.0
  {
    lem_log_ExistsUnique(b, x);    
    var y :| exp(b, y) == x;
    y
  } 

  /******************************************************************************
    log_b(x) and b^x are inverses of each other for x ∈ (0,∞) and b > 1
  ******************************************************************************/

  // b^(log_b(x)) = x 
  lemma lem_expLog_Inverse(b:real, x:real)
    requires b > 1.0 && x > 0.0
    ensures  exp(b, log(b, x)) == x
  {
    reveal log();
  }

  // log_b(b^x) = x 
  lemma lem_logExp_Inverse(b:real, x:real)
    requires b > 1.0
    requires exp(b, x) > 0.0
    ensures  log(b, exp(b, x)) == x 
  {
    // ensure the argument to log is in its domain:
    assert exp(b, x) > 0.0 by { lem_exp_Positive(b, x); }
    
    // Invoke existence and uniqueness on exp(b, x)
    ghost var v := exp(b, x);
    assert && (exists u :: exp(b, u) == v) 
           && (forall z1, z2 :: (exp(b, z1) == v) && (exp(b, z2) == v) ==> z1 == z2) 
      by { lem_log_ExistsUnique(b, v); }
    
    // From the def. of choose, the chosen y satisfies the predicate: 
    assert exp(b, log(b, exp(b, x))) == exp(b, x) by { reveal log(); }
  }

  // log and exp are mutual inverses on the domain x >= 1
  // ∀ y : log_b(x) = y ⟺ b^y = x 
  lemma lem_log_Inverse(b:real, x:real)
    requires b > 1.0 && x >= 1.0 
    ensures forall y :: (log(b, x) == y) <==> (exp(b, y) == x)
  { 
    forall y ensures (log(b, x) == y) <==> (exp(b, y) == x)
    {
      assert (log(b, x) == y) ==> (exp(b, y) == x) by {
        if log(b, x) == y {
          calc {
               exp(b, y);
            == exp(b, log(b, x));
            == { lem_expLog_Inverse(b, x); }
               x;      
          }
        }
      }
      assert (log(b, x) == y) <== (exp(b, y) == x) by {
        if exp(b, y) == x {
          calc {
               log(b, x);
            == log(b, exp(b, y));
            == { lem_logExp_Inverse(b, y); }
               y;      
          }          
        }
      }
    }
  }

  /******************************************************************************
    Derived properties
  ******************************************************************************/

  // b > 1 ∧ x > 1 ⟹ log_b(x) > 0
  lemma lem_log_Positive(b:real, x:real)
    requires b > 1.0 && x > 1.0 
    ensures  log(b, x) > 0.0 
  {
    var y := log(b, x);
    assert exp(b, y) == x > 1.0 by { reveal log(); }       
    assert exp(b, 0.0) == 1.0 by { lem_exp_Zero(b); }    
    assert exp(b, 0.0) < exp(b, y); 
    assert 0.0 < y by { lem_exp_StrictIncrIFF(b, y, 0.0); }    
  }

  lemma lem_log_PositiveAuto()
    ensures forall b:real, x:real :: 
            b > 1.0 && x > 1.0 ==> log(b, x) > 0.0
  {
    forall b:real, x:real | b > 1.0 && x > 1.0 
      ensures log(b, x) > 0.0
    {
      lem_log_Positive(b, x);
    }    
  }

  // b > 1 ∧ x >= 1 ⟹ log_b(x) >= 0
  lemma lem_log_NonNegative(b:real, x:real)
    requires b > 1.0 && x >= 1.0 
    ensures  log(b, x) >= 0.0 
  { 
    if x == 1.0 {
      assert log(b, 1.0) == 0.0 by { lem_log_One(b); }
    } else {
      lem_log_Positive(b, x);
    }
  }

  lemma lem_log_NonNegativeAuto()
    ensures forall b:real, x:real :: 
            b > 1.0 && x >= 1.0 ==> log(b, x) >= 0.0
  {
    forall b:real, x:real | b > 1.0 && x >= 1.0 
      ensures log(b, x) >= 0.0
    {
      lem_log_NonNegative(b, x);
    }    
  }

  // log_b(1) = 0
  lemma lem_log_One(b:real)
    requires b > 1.0
    ensures  log(b, 1.0) == 0.0
  { 
    calc {
           log(b, 1.0) == 0.0;
      <==> { lem_log_Inverse(b, 1.0); }
           exp(b, 0.0) == 1.0;
      <==> { lem_exp_Zero(b); }     
           true;
    }
  }

  // log_b(b) = 1
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
  
  // 1 < b <= x ⟹ log(b, x) >= 1
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

  // We can rewrite logarithms as a division of logarithms with the same base
  // log_b(x) = log_c(x) / log_c(b)
  lemma lem_log_ChangeOfBase(b:real, c:real, x:real)
    requires b > 1.0 && c > 1.0 && x > 0.0
    requires log(c, b) > 0.0
    ensures  log(b, x) == log(c, x) / log(c, b)
  {
    // Let y = log(b, x)
    var y := log(b, x);

    // Rewrite the log in exp form
    assert exp(b, y) == x by { lem_expLog_Inverse(b, x); }

    // Express b in terms of base c
    assert exp(c, log(c, b)) == b by { lem_expLog_Inverse(c, b); }

    // Substitute b for exp(c, log(c, b)) in exp(b, y)
    ghost var lg := log(c, b);
    calc {
         x;   
      == exp(exp(c, lg), y);
      == { lem_exp_Exp(c, lg, y); }
         exp(c, lg * y);
    }

    // We want to relate with log_c(x). We also have
    assert exp(c, log(c, x)) == x by { lem_expLog_Inverse(c, x); }

    // Now we have c^(log_c(b)*y)=x and c^log_c(x)=x.
    // By the uniqueness for base c: there is exactly one z with exp(c, z) == x
    lem_log_ExistsUnique(c, x);
    assert forall u, v :: exp(c, u) == x && exp(c, v) == x ==> u == v;

    // So we have
    assert log(c, x) == log(c, b) * y;

    // Rearrange desired equality
    assert y == log(b, x) == log(c, x) / log(c, b);
  }

  /******************************************************************************
    Order properties on the positive argument
  ******************************************************************************/
  
  // For base b > 1, log_b(x) is strictly increasing on argument x ∈ (0,∞)
  // b > 1 ∧ x,y > 0 ∧ x < y ⟹ log_b(x) < log_b(y)  
  lemma lem_log_StrictIncr(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 && y > 0.0 
    ensures  x < y ==> log(b, x) < log(b, y)
  {
    assert A: exp(b, log(b, x)) == x by { lem_expLog_Inverse(b, x); }
    assert B: exp(b, log(b, y)) == y by { lem_expLog_Inverse(b, y); }
    
    if x < y {
      assert exp(b, log(b, x)) < exp(b, log(b, y)) by { reveal A,B; }
      if !(log(b, x) < log(b, y)) {
        if log(b, x) == log(b, y) {
          assert exp(b, log(b, x)) == exp(b, log(b, y));
          assert false;
        } else if log(b, x) > log(b, y) {
          assert exp(b, log(b, x)) > exp(b, log(b, y)) 
            by { lem_exp_StrictIncrIFF(b, log(b, x), log(b, y)); }
          assert false; 
        }
      }
      assert log(b, x) < log(b, y);
    }
  }

  lemma lem_log_StrictIncrAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x > 0.0 && y > 0.0 && x < y ==> log(b, x) < log(b, y)
  {
    forall b:real, x:real, y:real | b > 1.0 && x > 0.0 && y > 0.0
      ensures x < y ==> log(b, x) < log(b, y)
    {
      lem_log_StrictIncr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // b > 1 ∧ x,y > 0 ∧ log_b(x) < log_b(y) ⟹ x < y   
  lemma lem_log_StrictIncrRev(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 && y > 0.0
    ensures  log(b, x) < log(b, y) ==> x < y
  {
    var log_b:real->real := (x => if x > 0.0 then log(b, x) else 0.0);
    assert forall x,y :: x > 0.0 && y > 0.0 ==> (x < y ==> log_b(x) < log_b(y))
      by { lem_log_StrictIncrAuto(); }
    lem_fun_StrictIncrIMPinjectiveRealPred(log_b, (x => x > 0.0));
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
  // b > 1 ∧ x,y > 0 ⟹ (x < y ⟺ log_b(x) < log_b(y))
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
  // b > 1 ∧ x,y > 0 ⟹ (x <= y ⟺ log_b(x) <= log_b(y))
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
  // b1,b2 > 1 ∧ x > 1 ∧ b1 < b2 ⟹ log_b1(x) > log_b2(x)
  lemma {:axiom} lem_log_BaseStrictDecr(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x > 1.0
    ensures  b1 < b2 ==> log(b1, x) > log(b2, x)     
  {
    // First let's define locally the log operation on fixed base 2
    ghost var log2:real-->real := x requires x > 0.0 => log(2.0, x);
    // Some facts for log2
    assert A : log2(x) > 0.0 
      by { lem_log_Positive(2.0, x); }
    assert B : log2(b1) > 0.0 
      by { lem_log_Positive(2.0, b1); }     
    assert C : b1 < b2 ==> log2(b1) < log2(b2)
      by { lem_log_StrictIncr(2.0, b1, b2); }

    // Now, for the proof
    if b1 < b2 {
      assert 0.0 < log2(x) by { reveal A; }
      assert 0.0 < log2(b1) < log2(b2) by { reveal B, C; }
      calc {
             log2(b1) < log2(b2);
        <==> log2(x) * log2(b1) < log2(x) * log2(b2);
        <==> log2(x) / log2(b2) < log2(x) / log2(b1);
        <==> log2(x) / log2(b1) > log2(x) / log2(b2);
        <==> { lem_log_ChangeOfBase(b1, 2.0, x);  }
             log(b1, x) > log2(x) / log2(b2);
        <==> { lem_log_ChangeOfBase(b2, 2.0, x);  }
             log(b1, x) > log(b2, x);             
      } 
    }
  }

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
  // b1,b2 > 1 ∧ x > 1 ∧ log_b1(x) > log_b2(x) ⟹ b1 < b2
  lemma lem_log_BaseStrictDecrRev(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x > 1.0
    ensures  log(b1, x) > log(b2, x) ==> b1 < b2
  {
    var log_x:real->real := (b => if b > 1.0 then log(b, x) else 0.0);
    assert forall b1,b2 :: b1 > 1.0 && b2 > 1.0 ==> (b1 < b2 ==> log_x(b1) > log_x(b2))
      by { lem_log_BaseStrictDecrAuto(); }
    lem_fun_StrictDecrIMPinjectiveRealPred(log_x, (b => b > 1.0));
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
  // b1,b2 > 1 ∧ x > 1 ⟹ (b1 < b2 ⟺ log_b1(x) > log_b2(x))
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
  // b1,b2 > 1 ∧ x > 1 ⟹ (b1 <= b2 ⟺ log_b1(x) >= log_b2(x))
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
  // b1,b2 > 1 ∧ x >= 1 ∧ b1 <= b2 ⟹ log_b1(x) >= log_b2(x)
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

}