/******************************************************************************
  Abstract Cost type
******************************************************************************/

module Cost {

  trait {:termination false} Cost<Input> {
    ghost var t:nat
    ghost const x:Input 

    ghost method Inc()
      modifies this
      ensures t == old(t)+1 
    {
      t := t + 1;
    }      

    ghost function Input(): Input reads this { x }

    ghost function Count(): nat reads this { t }   

    ghost function Size(): nat reads this
  }

}