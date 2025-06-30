include "./math/ExpReal.dfy"
include "./math/Factorial.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemBoundsNat.dfy"
include "./math/LemFunction.dfy"
include "./math/LogNat.dfy"
include "./math/Misc.dfy"
include "./math/SqrtNat.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityR0.dfy"

/**************************************************************************
  Common growth rates
**************************************************************************/

module GrowthRatesR0 { 
  import opened ExpReal
  import opened Factorial  
  import opened FloorCeil   
  import opened Misc 
  import opened LemBoundsNat
  import opened LemFunction
  import opened LogNat
  import opened SqrtNat
  import opened TypeR0 

  import opened ComplexityR0

  ghost function constGrowth() : nat->R0
  {   
    n => 1.0
  }

  ghost function logGrowth() : nat->R0
  {   
    n => if n>0 then log2(n) as R0 else 0.0
  }

  ghost function logGrowth2() : nat->R0
  {   
    n => log2(n+1) as R0
  }

  ghost function sqrtGrowth() : nat->R0
  {   
    n => sqrt(n) as R0
  }

  ghost function linGrowth() : nat->R0
  {   
    n => powr(n as R0, 1.0)
  }

  ghost function quadGrowth() : nat->R0
  {   
    n => powr(n as R0, 2.0)
  }

  ghost function cubicGrowth() : nat->R0
  {   
    n => powr(n as R0, 3.0)
  }

  ghost function polyGrowthR0(k:R0) : nat->R0
  {   
    n => powr(n as R0, k)
  }

  ghost function expGrowth() : nat->R0
  {   
    n => powr(2.0, n as R0)
  }

  ghost function facGrowth() : nat->R0
  {   
    n => fac(n) as R0
  }

  ghost function dexpGrowth() : nat->R0
  {   
    n => powr(2.0, powr(2.0, n as R0))
  }

}