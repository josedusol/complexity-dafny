
/**************************************************************************
  Power over non-negative integers
**************************************************************************/

module ExpNat {

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
    
}