
/**************************************************************************
  Square root over non-negative integers
**************************************************************************/

module SqrtNat {
  
  // sqrt(n)
  opaque ghost function sqrt(n:nat) : nat
    decreases n
  {
    if n == 0 
    then 0
    else var r := sqrt(n-1); 
         if (r+1)*(r+1) <= n
         then r + 1
         else r
  }

}