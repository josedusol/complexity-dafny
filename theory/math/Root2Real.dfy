include "./ExpReal.dfy"
include "./Root2Nat.dfy"
include "./RootReal.dfy"
include "./TypeR0.dfy"

/******************************************************************************
  Square root over non-negative reals
******************************************************************************/

module Root2Real {
  
  import N = Root2Nat
  import opened RootReal
  import opened TypeR0

  // sqrt(x) = root(x,2)
  opaque ghost function sqrt(x:R0) : R0
  { 
    lem_root_NonNegative(x, 2.0);
    root(x, 2.0)
  }  

  // Non-negativity
  // sqrt(x) >= 0
  lemma lem_sqrt_NonNegative(x:R0) 
    ensures sqrt(x) >= 0.0
  { 
    reveal sqrt();
    lem_root_NonNegative(x, 2.0);
  }

  // Monotonicity
  // x <= y ⇒ sqrt(x) <= sqrt(y)
  lemma lem_sqrt_BaseMonoIncr(x:R0, y:R0)
    ensures  x <= y ==> sqrt(x) <= sqrt(y) // TODO
//   {
//     //lem_root_BaseMonoIncr(x, 2.0);
//   }

//   // Monotonicity in the index
//   // 0 < p <= q ∧ x >= 0 ⇒ root(x,p) >= root(x,q)
//   lemma {:axiom} lem_sqrt_IndexMonoIncr(x:real, p:real, q:real)
//     requires 0.0 < p <= q && x >= 0.0
//     ensures root(x,p) >= root(x,q)
//     // TODO  

}