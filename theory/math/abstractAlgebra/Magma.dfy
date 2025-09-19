/******************************************************************************
  Magma structure (T,⊗)
******************************************************************************/

abstract module Magma {
  
  // Abstract domain
  type T

  // Closed binary operation 
  // _⊗_ : TxT → T
  function op(x:T, y:T): T

}