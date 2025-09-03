/******************************************************************************
  Abstract Cost type
******************************************************************************/

module Cost2 {

  trait {:ghost} {:termination false} Cost2<OpType, State> {
    ghost var ops: seq<OpType>
    ghost var totalCost: nat

    ghost method Log(op:OpType, weight:nat := 1)
      modifies this
      ensures ops == old(ops) + [op]
      ensures totalCost == old(totalCost) + weight
    {
      ops := ops + [op];
      totalCost := totalCost + weight;
    }

    ghost function Count(): nat
      reads this
    {
      totalCost
    }

    ghost predicate OpsValid(init:State)
      reads this

    // Abstract: replay the operations on the initial state
    ghost function ApplyOps(init:State): State
      reads this
      requires OpsValid(init)
  }

}