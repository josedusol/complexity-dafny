/******************************************************************************
  Recurrences
******************************************************************************/

module Recurrence {
  
  // Downward recurrence body
  opaque ghost function recDwBody(c:real, f:nat->real, g:real->real, n:nat) : real
  {    
    if   n == 0 
    then c
    else g(f(n - 1))   
  }  

  // Upward recurrence body 
  opaque ghost function recUpBody(c:real, f:(nat,nat)->real, g:real->real, n:nat, i:nat) : real
  {    
    if   i < n 
    then g(f(n, i+1))   
    else c
  }            
    
  // Downward and Upward recurrences are identical for any i <= n
  lemma lem_rec_dwEQupAti(c:real, g:real->real, Fdw:nat->real, Fup:(nat,nat)->real, n:nat, i:nat)
    requires i <= n
    requires forall n :: Fdw(n) == recDwBody(c, Fdw, g, n) 
    requires forall n:nat, i:nat :: Fup(n,i) == recUpBody(c, Fup, g, n, i) 
    ensures  Fdw(n - i) == Fup(n, i)
    decreases n - i
  {
    if i == n {
       reveal recDwBody(), recUpBody();
    } else {
      calc {
           Fdw(n - i);
        == { reveal recDwBody; }
           g(Fdw((n - i) - 1)); 
        == g(Fdw(n - (i + 1))); 
        == { lem_rec_dwEQupAti(c, g, Fdw, Fup, n, i+1); }
           g(Fup(n, i + 1)); 
        == { reveal recUpBody; } 
           Fup(n, i);   
      }
    }
  }

  // Downward and Upward recurrences are identical
  lemma lem_rec_dwEQup(c:real, g:real->real, Fdw:nat->real, Fup:(nat,nat)->real)
    requires forall n:nat :: Fdw(n) == recDwBody(c, Fdw, g, n) 
    requires forall n:nat, i:nat :: Fup(n,i) == recUpBody(c, Fup, g, n, i) 
    ensures  forall n:nat :: Fdw(n) == Fup(n, 0)
  {
    forall n:nat
      ensures Fdw(n) == Fup(n, 0)
    {
      lem_rec_dwEQupAti(c, g, Fdw, Fup, n, 0);
    }
  }

}