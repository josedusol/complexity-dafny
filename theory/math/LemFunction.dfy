include "./TypeR0.dfy"

/******************************************************************************
  Functions
******************************************************************************/

module LemFunction {
  import opened TypeR0

  ghost function liftD<T>(f:nat->T, default:T) : int->T
  {
    k => if k < 0 then default else f(k as nat)
  }

  ghost function liftCi2r(f:int->int) : int->real
  {
    n => f(n) as real
  }

  // Lift f:nat->nat to f':nat->R0
  ghost function liftToR0(f:nat->nat) : nat->R0
  {
    n => f(n) as R0
  }

  lemma {:axiom} lem_funExt<A,B>(f1:A->B, f2:A->B)
    requires forall x:A :: f1(x) == f2(x)
    ensures f1 == f2

  lemma lem_etaApp<A,B>(f:A->B)
    ensures forall x:A :: f == (x => f(x))
  { 
    lem_funExt(f, x => f(x)); 
  }

  lemma lem_funExtProd<A,B>(f1:A->real, g1:A->real, f2:A->real, g2:A->real)
    requires forall x:A :: f1(x) == f2(x)
    requires forall x:A :: g1(x) == g2(x)
    ensures (x => f1(x)*g1(x)) == (x => f2(x)*g2(x))
  { 
    lem_funExt(x => f1(x)*g1(x), x => f2(x)*g2(x)) by { 
      forall x:A
         ensures (x => f1(x)*g1(x))(x) == (x => f2(x)*g2(x))(x)
      {
      }
    }
  }
}