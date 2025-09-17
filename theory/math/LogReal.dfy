include "./ExpReal.dfy"
include "./LemFunction.dfy"

/******************************************************************************
  Logarithm over reals
******************************************************************************/

module LogReal {

  import Exp = ExpReal
  import opened LemFunction

  // There is exactly one y such that b^y = x
  lemma {:axiom} lem_ExistsUnique(b:real, x:real)
    requires b > 1.0 && x > 0.0
    ensures  exists y :: Exp.exp(b, y) == x
    ensures  forall z1, z2 :: Exp.exp(b, z1) == x && Exp.exp(b, z2) == x ==> z1 == z2
    // Proof.
    // Existence by intermediate value theorem
    // Uniquenes by injectivity implied by strictly increasing growth

  // log_b(x) = the unique y such that exp(b,y) = x
  opaque ghost function log(b:real, x:real) : real
    requires b > 1.0 && x > 0.0
  {
    lem_ExistsUnique(b, x);    
    var y :| Exp.exp(b, y) == x;
    y
  } 

  /******************************************************************************
    log_b(x) and b^x are inverses of each other for x ∈ (0,∞) and b > 1
  ******************************************************************************/

  // b^(log_b(x)) = x 
  lemma lem_ExpLogInverse(b:real, x:real)
    requires b > 1.0 && x > 0.0
    ensures  Exp.exp(b, log(b, x)) == x
  {
    reveal log();
  }

  // log_b(b^x) = x 
  lemma lem_LogExpInverse(b:real, x:real)
    requires b > 1.0
    requires Exp.exp(b, x) > 0.0
    ensures  log(b, Exp.exp(b, x)) == x 
  {
    // ensure the argument to log is in its domain:
    assert Exp.exp(b, x) > 0.0 by { Exp.lem_Positive(b, x); }
    
    // Invoke existence and uniqueness on exp(b, x)
    ghost var v := Exp.exp(b, x);
    assert && (exists u :: Exp.exp(b, u) == v) 
           && (forall z1, z2 :: (Exp.exp(b, z1) == v) && (Exp.exp(b, z2) == v) ==> z1 == z2) 
      by { lem_ExistsUnique(b, v); }
    
    // From the def. of choose, the chosen y satisfies the predicate: 
    assert Exp.exp(b, log(b, Exp.exp(b, x))) == Exp.exp(b, x) by { reveal log(); }
  }

  // log and exp are mutual inverses on the domain x >= 1
  // ∀ y : log_b(x) = y ⟺ b^y = x 
  lemma lem_MutualInverse(b:real, x:real)
    requires b > 1.0 && x >= 1.0 
    ensures forall y :: (log(b, x) == y) <==> (Exp.exp(b, y) == x)
  { 
    forall y ensures (log(b, x) == y) <==> (Exp.exp(b, y) == x)
    {
      assert (log(b, x) == y) ==> (Exp.exp(b, y) == x) by {
        if log(b, x) == y {
          calc {
               Exp.exp(b, y);
            == Exp.exp(b, log(b, x));
            == { lem_ExpLogInverse(b, x); }
               x;      
          }
        }
      }
      assert (log(b, x) == y) <== (Exp.exp(b, y) == x) by {
        if Exp.exp(b, y) == x {
          calc {
               log(b, x);
            == log(b, Exp.exp(b, y));
            == { lem_LogExpInverse(b, y); }
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
  lemma lem_Positive(b:real, x:real)
    requires b > 1.0 && x > 1.0 
    ensures  log(b, x) > 0.0 
  {
    var y := log(b, x);
    assert Exp.exp(b, y) == x > 1.0 by { reveal log(); }       
    assert Exp.exp(b, 0.0) == 1.0 by { Exp.lem_Zero(b); }    
    assert Exp.exp(b, 0.0) < Exp.exp(b, y); 
    assert 0.0 < y by { Exp.lem_StrictIncrIFF(b, y, 0.0); }    
  }

  lemma lem_PositiveAuto()
    ensures forall b:real, x:real :: 
            b > 1.0 && x > 1.0 ==> log(b, x) > 0.0
  {
    forall b:real, x:real | b > 1.0 && x > 1.0 
      ensures log(b, x) > 0.0
    {
      lem_Positive(b, x);
    }    
  }

  // b > 1 ∧ x >= 1 ⟹ log_b(x) >= 0
  lemma lem_NonNegative(b:real, x:real)
    requires b > 1.0 && x >= 1.0 
    ensures  log(b, x) >= 0.0 
  { 
    if x == 1.0 {
      assert log(b, 1.0) == 0.0 by { lem_One(b); }
    } else {
      lem_Positive(b, x);
    }
  }

  lemma lem_NonNegativeAuto()
    ensures forall b:real, x:real :: 
            b > 1.0 && x >= 1.0 ==> log(b, x) >= 0.0
  {
    forall b:real, x:real | b > 1.0 && x >= 1.0 
      ensures log(b, x) >= 0.0
    {
      lem_NonNegative(b, x);
    }    
  }

  // log_b(1) = 0
  lemma lem_One(b:real)
    requires b > 1.0
    ensures  log(b, 1.0) == 0.0
  { 
    calc {
           log(b, 1.0) == 0.0;
      <==> { lem_MutualInverse(b, 1.0); }
           Exp.exp(b, 0.0) == 1.0;
      <==> { Exp.lem_Zero(b); }     
           true;
    }
  }

  // log_b(b) = 1
  lemma lem_Base(b:real)
    requires b > 1.0
    ensures  log(b, b) == 1.0    
  {
    calc {
           true;
      <==> { Exp.lem_One(b); }
           Exp.exp(b, 1.0) == b;
      ==>  log(b, Exp.exp(b, 1.0)) == log(b, b);
      <==> { lem_LogExpInverse(b, 1.0); }
           1.0 == log(b, b);
    }
  }
  
  // 1 < b <= x ⟹ log(b, x) >= 1
  lemma lem_GEQone(b:real, x:real)
    requires 1.0 < b <= x
    ensures  log(b, x) >= 1.0
  {
    calc {
           b <= x;
      ==>  { lem_MonoIncrIFF(b, b, x); }
           log(b, x) >= log(b, b); 
      <==> { lem_Base(b); }
           log(b, x) >= 1.0;
    }
  }  

  // We can rewrite logarithms as a division of logarithms with the same base
  // log_b(x) = log_c(x) / log_c(b)
  lemma lem_ChangeOfBase(b:real, c:real, x:real)
    requires b > 1.0 && c > 1.0 && x > 0.0
    requires log(c, b) > 0.0
    ensures  log(b, x) == log(c, x) / log(c, b)
  {
    // Let y = log(b, x)
    var y := log(b, x);

    // Rewrite the log in exp form
    assert Exp.exp(b, y) == x by { lem_ExpLogInverse(b, x); }

    // Express b in terms of base c
    assert Exp.exp(c, log(c, b)) == b by { lem_ExpLogInverse(c, b); }

    // Substitute b for exp(c, log(c, b)) in exp(b, y)
    ghost var lg := log(c, b);
    calc {
         x;   
      == Exp.exp(Exp.exp(c, lg), y);
      == { Exp.lem_Exp(c, lg, y); }
         Exp.exp(c, lg * y);
    }

    // We want to relate with log_c(x). We also have
    assert Exp.exp(c, log(c, x)) == x by { lem_ExpLogInverse(c, x); }

    // Now we have c^(log_c(b)*y)=x and c^log_c(x)=x.
    // By the uniqueness for base c: there is exactly one z with exp(c, z) == x
    lem_ExistsUnique(c, x);
    assert forall u, v :: Exp.exp(c, u) == x && Exp.exp(c, v) == x ==> u == v;

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
  lemma lem_StrictIncr(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 && y > 0.0 
    ensures  x < y ==> log(b, x) < log(b, y)
  {
    assert A: Exp.exp(b, log(b, x)) == x by { lem_ExpLogInverse(b, x); }
    assert B: Exp.exp(b, log(b, y)) == y by { lem_ExpLogInverse(b, y); }
    
    if x < y {
      assert Exp.exp(b, log(b, x)) < Exp.exp(b, log(b, y)) by { reveal A,B; }
      if !(log(b, x) < log(b, y)) {
        if log(b, x) == log(b, y) {
          assert Exp.exp(b, log(b, x)) == Exp.exp(b, log(b, y));
          assert false;
        } else if log(b, x) > log(b, y) {
          assert Exp.exp(b, log(b, x)) > Exp.exp(b, log(b, y)) 
            by { Exp.lem_StrictIncrIFF(b, log(b, x), log(b, y)); }
          assert false; 
        }
      }
      assert log(b, x) < log(b, y);
    }
  }

  lemma lem_StrictIncrAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x > 0.0 && y > 0.0 && x < y ==> log(b, x) < log(b, y)
  {
    forall b:real, x:real, y:real | b > 1.0 && x > 0.0 && y > 0.0
      ensures x < y ==> log(b, x) < log(b, y)
    {
      lem_StrictIncr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // b > 1 ∧ x,y > 0 ∧ log_b(x) < log_b(y) ⟹ x < y   
  lemma lem_StrictIncrREV(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 && y > 0.0
    ensures  log(b, x) < log(b, y) ==> x < y
  {
    var log_b:real->real := (x => if x > 0.0 then log(b, x) else 0.0);
    assert forall x,y :: x > 0.0 && y > 0.0 ==> (x < y ==> log_b(x) < log_b(y))
      by { lem_StrictIncrAuto(); }
    lem_StrictIncrImpInjectiveRealPred(log_b, (x => x > 0.0));
    assert forall x,y :: x > 0.0 && y > 0.0 ==> (log_b(x) < log_b(y) ==> x < y);
    assert forall x :: x > 0.0 ==> log_b(x) == log(b, x);    
  }

  lemma lem_StrictIncrREVAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x > 0.0 && y > 0.0 && log(b, x) < log(b, y) ==> x < y
  {
    forall b:real, x:real, y:real | b > 1.0 && x > 0.0 && y > 0.0
      ensures log(b, x) < log(b, y) ==> x < y
    {
      lem_StrictIncrREV(b, x, y);
    }       
  }

  // Join previous facts into an equivalence
  // b > 1 ∧ x,y > 0 ⟹ (x < y ⟺ log_b(x) < log_b(y))
  lemma lem_StrictIncrIFF(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 && y > 0.0
    ensures  x < y <==> (log(b, x) < log(b, y))
  { 
    lem_StrictIncr(b,x,y);
    lem_StrictIncrREV(b,x,y);
  }  

  lemma lem_StrictIncrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x > 0.0 && y > 0.0 ==> (x < y <==> log(b, x) < log(b, y))
  {
    forall b:real, x:real, y:real | b > 1.0 && x > 0.0 && y > 0.0
      ensures x < y <==> log(b, x) < log(b, y)
    {
      lem_StrictIncrIFF(b, x, y);
    }       
  }

  // Weak version of lem_StrictIncrIFF
  // b > 1 ∧ x,y > 0 ⟹ (x <= y ⟺ log_b(x) <= log_b(y))
  lemma lem_MonoIncrIFF(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 && y > 0.0
    ensures  x <= y <==> (log(b, x) <= log(b, y))
  { 
    lem_StrictIncrIFFAuto();
  }

  lemma lem_MonoIncrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x > 0.0 && y > 0.0 ==> (x <= y <==> log(b, x) <= log(b, y))
  {
    forall b:real, x:real, y:real | b > 1.0 && x > 0.0 && y > 0.0
      ensures x <= y <==> log(b, x) <= log(b, y)
    {
      lem_MonoIncrIFF(b, x, y);
    }       
  }  

  /******************************************************************************
    Order properties on the base
  ******************************************************************************/

  // When x ∈ (1,∞), log_b(x) is strictly decreasing on b
  // b1,b2 > 1 ∧ x > 1 ∧ b1 < b2 ⟹ log_b1(x) > log_b2(x)
  lemma lem_BaseStrictDecr(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x > 1.0
    ensures  b1 < b2 ==> log(b1, x) > log(b2, x)     
  {
    // First let's define locally the log operation on fixed base 2
    ghost var log2:real-->real := x requires x > 0.0 => log(2.0, x);
    // Some facts for log2
    assert A : log2(x) > 0.0 
      by { lem_Positive(2.0, x); }
    assert B : log2(b1) > 0.0 
      by { lem_Positive(2.0, b1); }     
    assert C : b1 < b2 ==> log2(b1) < log2(b2)
      by { lem_StrictIncr(2.0, b1, b2); }

    // Now, for the proof
    if b1 < b2 {
      assert 0.0 < log2(x) by { reveal A; }
      assert 0.0 < log2(b1) < log2(b2) by { reveal B, C; }
      calc {
             log2(b1) < log2(b2);
        <==> log2(x) * log2(b1) < log2(x) * log2(b2);
        <==> log2(x) / log2(b2) < log2(x) / log2(b1);
        <==> log2(x) / log2(b1) > log2(x) / log2(b2);
        <==> { lem_ChangeOfBase(b1, 2.0, x);  }
             log(b1, x) > log2(x) / log2(b2);
        <==> { lem_ChangeOfBase(b2, 2.0, x);  }
             log(b1, x) > log(b2, x);             
      } 
    }
  }

  lemma lem_BaseStrictDecrAuto()
    ensures forall b1:real, b2:real, x:real :: 
      b1 > 1.0 && b2 > 1.0 && x > 1.0 && b1 < b2 ==> log(b1, x) > log(b2, x)   
  {
    forall b1:real, b2:real, x:real | b1 > 1.0 && b2 > 1.0 && x > 1.0
      ensures b1 < b2 ==> log(b1, x) > log(b2, x)  
    {
      lem_BaseStrictDecr(b1, b2, x);
    }       
  }

  // Previous fact is reversible
  // b1,b2 > 1 ∧ x > 1 ∧ log_b1(x) > log_b2(x) ⟹ b1 < b2
  lemma lem_BaseStrictDecrREV(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x > 1.0
    ensures  log(b1, x) > log(b2, x) ==> b1 < b2
  {
    var log_x:real->real := (b => if b > 1.0 then log(b, x) else 0.0);
    assert forall b1,b2 :: b1 > 1.0 && b2 > 1.0 ==> (b1 < b2 ==> log_x(b1) > log_x(b2))
      by { lem_BaseStrictDecrAuto(); }
    lem_StrictDecrImpInjectiveRealPred(log_x, (b => b > 1.0));
    assert forall b1,b2 :: b1 > 1.0 && b2 > 1.0 ==> (log_x(b1) > log_x(b2) ==> b1 < b2);
    assert forall b :: b > 1.0 ==> log_x(b) == log(b, x);       
  } 

  lemma lem_BaseStrictDecrREVAuto()
    ensures forall b1:real, b2:real, x:real :: 
      b1 > 1.0 && b2 > 1.0 && x > 1.0 && log(b1, x) > log(b2, x) ==> b1 < b2  
  {
    forall b1:real, b2:real, x:real | b1 > 1.0 && b2 > 1.0 && x > 1.0
      ensures log(b1, x) > log(b2, x) ==> b1 < b2 
    {
      lem_BaseStrictDecrREV(b1, b2, x);
    }       
  }

  // Join previous facts into an equivalence
  // b1,b2 > 1 ∧ x > 1 ⟹ (b1 < b2 ⟺ log_b1(x) > log_b2(x))
  lemma lem_BaseStrictDecrIFF(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x > 1.0
    ensures  b1 < b2 <==> log(b1, x) > log(b2, x)
  { 
    lem_BaseStrictDecr(b1, b2, x);
    lem_BaseStrictDecrREV(b1, b2, x);
  }

  lemma lem_BaseStrictDecrIFFAuto()
    ensures forall b1:real, b2:real, x:real :: 
      b1 > 1.0 && b2 > 1.0 && x > 1.0 ==> (b1 < b2 <==> log(b1, x) > log(b2, x))   
  {
    forall b1:real, b2:real, x:real | b1 > 1.0 && b2 > 1.0 && x > 1.0
      ensures b1 < b2 <==> log(b1, x) > log(b2, x)  
    {
      lem_BaseStrictDecrIFF(b1, b2, x);
    }       
  }

  // Weak version of lem_BaseStrictDecrIFF
  // b1,b2 > 1 ∧ x > 1 ⟹ (b1 <= b2 ⟺ log_b1(x) >= log_b2(x))
  lemma lem_BaseMonoDecrIFF(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x > 1.0
    ensures  b1 <= b2 <==> log(b1, x) >= log(b2, x)  
  {
    lem_BaseStrictDecrIFFAuto();
  }  

  lemma lem_BaseMonoDecrIFFAuto()
    ensures forall b1:real, b2:real, x:real :: 
      b1 > 1.0 && b2 > 1.0 && x > 1.0 ==> (b1 <= b2 <==> log(b1, x) >= log(b2, x))   
  {
    forall b1:real, b2:real, x:real | b1 > 1.0 && b2 > 1.0 && x > 1.0
      ensures b1 <= b2 <==> log(b1, x) >= log(b2, x)  
    {
      lem_BaseMonoDecrIFF(b1, b2, x);
    }       
  }

  // Weak version of lem_BaseStrictDecr, but also holds when x=1
  // b1,b2 > 1 ∧ x >= 1 ∧ b1 <= b2 ⟹ log_b1(x) >= log_b2(x)
  lemma lem_BaseMonoDecr(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x >= 1.0
    ensures  b1 <= b2 ==> log(b1, x) >= log(b2, x)  
  {
    if x == 1.0 {
      lem_One(b1);
      lem_One(b2);
    } else if x > 1.0 {
      lem_BaseStrictDecr(b1, b2, x);
    }
  }

  lemma lem_BaseMonoDecrAuto()
    ensures forall b1:real, b2:real, x:real :: 
      b1 > 1.0 && b2 > 1.0 && x >= 1.0 && b1 <= b2 ==> log(b1, x) >= log(b2, x)   
  {
    forall b1:real, b2:real, x:real | b1 > 1.0 && b2 > 1.0 && x >= 1.0
      ensures b1 <= b2 ==> log(b1, x) >= log(b2, x)  
    {
      lem_BaseMonoDecr(b1, b2, x);
    }       
  }

}