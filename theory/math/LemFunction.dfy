
/**************************************************************************
  Functions
**************************************************************************/

module LemFunction {

  lemma {:axiom} lem_funExt<A,B>(f1:A->B, f2:A->B)
    requires forall x:A :: f1(x) == f2(x)
    ensures f1 == f2

}