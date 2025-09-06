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

  lemma {:axiom} lem_fun_Ext<A,B>(f1:A->B, f2:A->B)
    requires forall x:A :: f1(x) == f2(x)
    ensures f1 == f2

  lemma lem_fun_EtaApp<A,B>(f:A->B)
    ensures forall x:A :: f == (x => f(x))
  { 
    lem_fun_Ext(f, x => f(x)); 
  }

  lemma lem_funExtProd<A,B>(f1:A->real, g1:A->real, f2:A->real, g2:A->real)
    requires forall x:A :: f1(x) == f2(x)
    requires forall x:A :: g1(x) == g2(x)
    ensures (x => f1(x)*g1(x)) == (x => f2(x)*g2(x))
  { 
    lem_fun_Ext(x => f1(x)*g1(x), x => f2(x)*g2(x)) by { 
      forall x:A
         ensures (x => f1(x)*g1(x))(x) == (x => f2(x)*g2(x))(x)
      {
      }
    }
  }

  // If f is strictly increasing then f is injective
  lemma lem_fun_StrictIncrIMPinjective(f:real->real)
    requires forall x, y :: x < y ==> f(x) < f(y)
    ensures  forall x, y :: f(x) == f(y) ==> x == y
  {
  }

  lemma lem_fun_StrictIncrIMPinjectivePred(f:real->real, p:real->bool)
    requires forall x, y :: p(x) && p(y) ==> (x < y ==> f(x) < f(y))
    ensures  forall x, y :: p(x) && p(y) ==> (f(x) == f(y) ==> x == y)
  {
  }    

  // If f is strictly decreasing then f is injective
  lemma lem_fun_StrictDecrIMPinjective(f:real->real)
    requires forall x, y :: x < y ==> f(x) > f(y)
    ensures  forall x, y :: f(x) == f(y) ==> x == y
  {
  }

  lemma lem_fun_StrictDecrIMPinjectivePred(f:real->real, p:real->bool)
    requires forall x, y :: p(x) && p(y) ==> (x < y ==> f(x) > f(y))
    ensures  forall x, y :: p(x) && p(y) ==> (f(x) == f(y) ==> x == y)
  {
  } 

}