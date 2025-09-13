include "./Order.dfy"
include "./Order2.dfy"
include "./TypeR0.dfy"

/******************************************************************************
  Functions
******************************************************************************/

module LemFunction {

  import opened Order
  //import Order2
  import opened TypeR0

  /******************************************************************************
    Liftings
  ******************************************************************************/

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

  /******************************************************************************
    Extensionality
  ******************************************************************************/

  lemma {:axiom} lem_fun_Ext<A,B>(f1:A->B, f2:A->B)
    requires forall x:A :: f1(x) == f2(x)
    ensures f1 == f2

  lemma lem_fun_EtaApp<A,B>(f:A->B)
    ensures forall x:A :: f == (x => f(x))
  { 
    lem_fun_Ext(f, x => f(x)); 
  }

  lemma lem_fun_ExtProd<A,B>(f1:A->real, g1:A->real, f2:A->real, g2:A->real)
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

  /******************************************************************************
    If f:A->A is strictly increasing/decreasing then f is injective
  ******************************************************************************/

  // General version for any A equipt with Ord<A>
  lemma lem_fun_StrictIncrIMPinjective<A>(f:A->A, ord:Ord<A>)
    requires forall x, y :: ord.Lt(x, y) ==> ord.Lt(f(x), f(y))
    ensures  forall x, y :: f(x) == f(y) ==> x == y
  {
    forall x, y | f(x) == f(y)
      ensures x == y
    {
      // By RAA, suppose x != y
      if x != y {
        ord.lem_Lt_IfNotEq(x, y); // (x < y) ∨ (y < x) 
        if ord.Lt(x, y) {
          assert ord.Lt(f(x), f(y));
          assert f(x) != f(y) by { ord.lem_Lt_NotEq(f(x), f(y)); }
          assert false;
        }
        else if ord.Lt(y, x) {
          assert ord.Lt(f(y), f(x));
          assert f(x) != f(y) by { ord.lem_Lt_NotEq(f(x), f(y)); }
          assert false;
        }
      }
    }
  }

  lemma lem_fun_StrictDecrIMPinjective<A>(f:A->A, ord:Ord<A>)
    requires forall x, y :: ord.Lt(x, y) ==> ord.Gt(f(x), f(y))
    ensures  forall x, y :: f(x) == f(y) ==> x == y
  {
    forall x, y | f(x) == f(y)
      ensures x == y
    {
      // By RAA, suppose x != y
      if x != y {
        ord.lem_Lt_IfNotEq(x, y); // (x < y) ∨ (y < x) 
        if ord.Lt(x, y) {
          assert ord.Gt(f(x), f(y));
          assert ord.Lt(f(y), f(x));
          assert f(x) != f(y) by { ord.lem_Lt_NotEq(f(x), f(y)); }
          assert false;
        }
        else if ord.Lt(y, x) {
          assert ord.Gt(f(y), f(x));
          assert ord.Lt(f(x), f(y));
          assert f(x) != f(y) by { ord.lem_Lt_NotEq(f(x), f(y)); }
          assert false;
        }
      }
    }
  }

  // Concrete version for Dafny primitive real type
  lemma lem_fun_StrictIncrIMPinjectiveReal(f:real->real)
    requires forall x, y :: x < y ==> f(x) < f(y)
    ensures  forall x, y :: f(x) == f(y) ==> x == y
  {
  }

  lemma lem_fun_StrictIncrIMPinjectiveRealPred(f:real->real, p:real->bool)
    requires forall x, y :: p(x) && p(y) ==> (x < y ==> f(x) < f(y))
    ensures  forall x, y :: p(x) && p(y) ==> (f(x) == f(y) ==> x == y)
  {
  }    

  lemma lem_fun_StrictDecrIMPinjectiveReal(f:real->real)
    requires forall x, y :: x < y ==> f(x) > f(y)
    ensures  forall x, y :: f(x) == f(y) ==> x == y
  {
  }

  lemma lem_fun_StrictDecrIMPinjectiveRealPred(f:real->real, p:real->bool)
    requires forall x, y :: p(x) && p(y) ==> (x < y ==> f(x) > f(y))
    ensures  forall x, y :: p(x) && p(y) ==> (f(x) == f(y) ==> x == y)
  {
  } 

  // Concrete version for Dafny primitive nat type
  lemma lem_fun_StrictIncrIMPinjectiveNat(f:nat->nat)
    requires forall x, y :: x < y ==> f(x) < f(y)
    ensures  forall x, y :: f(x) == f(y) ==> x == y
  {
  }

}