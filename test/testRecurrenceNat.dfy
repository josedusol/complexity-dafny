include "../theory/math/Recurrence.dfy"

import opened Recurrence

opaque ghost function f1(n:nat) : nat
  decreases n 
{   
  if n == 0 then 1 else f1(n-1) + 2
} 

opaque ghost function f2(n:nat, i:nat) : nat
  decreases n - i
{   
  if i < n then f2(n, i+1) + 2 else 1
} 

lemma lem_f1def(n:nat)
  ensures n == 0 ==> f1(n) == 1
  ensures n != 0 ==> f1(n) == f1(n-1) + 2
{
  reveal f1();
} 

lemma lem_f2def(n:nat, i:nat)
  ensures i >= n ==> f2(n,i) == 1
  ensures i < n  ==> f2(n,i) == f2(n, i+1) + 2
  decreases n - i
{
  reveal f2();
}

lemma lem_test() 
  ensures forall n :: f1(n) == f2(n,0)
{
  var g:real->real := x => x + 2.0;
  var f1':nat->real := (n:nat) => f1(n) as real;
  var f2':(nat,nat)->real := (n:nat,i:nat) => f2(n,i) as real;
  forall n:nat 
      ensures f1(n) as real == recDwBody(1.0, f1', g, n)
  {
      reveal recDwBody;
      lem_f1def(n);    
  }
  forall n:nat, i:nat
      ensures f2(n,i) as real == recUpBody(1.0, f2', g, n, i)
  {
      reveal recUpBody;
      lem_f2def(n, i);
  }

  lem_rec_dwEQup(1.0, g, f1', f2'); 
}