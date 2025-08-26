include "../../../theory/math/ExpReal.dfy"
include "../../../theory/ComplexityR0.dfy"
include "./List.dfy"

/******************************************************************************
  Array implementation of a List
******************************************************************************/

module ArrayList refines List {

  import opened ExpReal
  import opened ComplexityR0

  class ArrayList<T(0)> extends List<T> {

    var arr:array<T>
    var n:nat
    ghost var elems:seq<T>  // ghost model for physical array arr

    constructor(capacity:nat)
      // Pre:
      requires capacity > 0
      // Post:      
      ensures Valid()
      ensures arr.Length == capacity
      ensures Size() == 0
    {
      arr := new T[capacity];  
      n := 0; 
      elems := [];
    }   

    /******************************************************************************
      Query operations
    ******************************************************************************/

    // Returns the size of the list
    function Size(): nat
      reads this, Repr()
      // Pre:
      requires Valid()
    {
      n
    }

    // Returns the element at position i in the list
    function Get(i:nat): (ret: (T, ghost R0))    
      reads this, Repr()
      // Pre:
      requires Valid()
      requires i < Size() 
      // Complexity:
      ensures var t := ret.1; t <= costGet(Size())
      ensures var t := ret.1; tIsBigO(Size(), t as R0, constGrowth())      
    {
      lem_costGetBigOconst();
      (arr[i], ghost 1.0)
    }

    // Returns the set of heap objects that are part of this data structure's representation
    function Repr(): set<object>
      reads this
    {
      {this, arr}
    }    

    // Returns true iff the data structure's invariant holds
    ghost predicate Valid()
      reads this, Repr()
    {
      && 0 <= n <= arr.Length
      && 0 < arr.Length
      && this in Repr() 
      && arr  in Repr()
      // The array and its ghost counterpart are aligned
      && n == |elems| 
      && (forall i :: 0 <= i < n ==> arr[i] == elems[i])
    }    

    // Returns true iff the array is full
    predicate Full()
      reads this, Repr()
      // Pre:
      requires Valid()
    {
      n == arr.Length
    }    

    /******************************************************************************
      Update operations
    ******************************************************************************/

    // Inserts element x at position k in the list
    method Insert(k:nat, x:T) returns (ghost t:R0)
      modifies this, Repr()    
      // Pre:      
      requires Valid()
      requires 0 <= k <= Size()
      requires !Full()
      // Post:      
      ensures  Valid() && fresh(Repr() - old(Repr()))
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < k           ==> Get(j).0 == old(Get(j).0)    // [0, k) is unchanged  
      ensures  forall j :: k < j <= old(Size()) ==> Get(j).0 == old(Get(j-1).0)  // (k, n] is right shifted 
      ensures  Get(k).0 == x                                                     // xs[k] == x
      // Complexity:
      ensures  var N := old(Size()); && t == costInsert(N-k)
                                     && tIsBigO(N, t as R0, linGrowth())
    {
      // Update model
      elems := elems[..k] + [x] + elems[k..];
      // Update array:
      // 1. Shift (k, n] to the right
      t := 0.0;
      var i := n;
      while i > k
        modifies arr
        invariant k <= i <= n < arr.Length    
        invariant forall j :: 0 <= j <= k ==> arr[j] == old(arr[j])    // [0, k] is unchanged  
        invariant forall j :: i <  j <= n ==> arr[j] == old(arr[j-1])  // (i, n] is already shifted  
        invariant forall j :: k <= j < i  ==> arr[j] == old(arr[j])    // [k, i) still equals old      
        invariant t == (n - i) as R0
        decreases i
      {
        arr[i] := arr[i-1]; // shift right
        i := i - 1;
        t := t + 1.0;
      }
      // 2. Insert x at position k
      assert i == k;
      arr[k] := x;
      assert t == (n - k) as R0 
               <= costInsert(n);
      assert costInsert in O(linGrowth()) by { var c, n0 := lem_costInsertBigOlin(); }      
      n := n + 1;
      assert forall j :: 0 <= j < |elems| ==> arr[j] == elems[j];
    }

    // Deletes element at position k in the list
    method Delete(k:nat) returns (ghost t:R0)
      modifies this, Repr()
      // Pre:    
      requires Valid()
      requires 0 <= k < Size()
      // Post:
      ensures  Valid() && fresh(Repr() - old(Repr()))
      ensures  Size() == old(Size()) - 1
      ensures  forall j :: 0 <= j < k      ==> Get(j).0 == old(Get(j).0)
      ensures  forall j :: k <= j < Size() ==> Get(j).0 == old(Get(j+1).0)   
      // Complexity:
      ensures  var N := old(Size()); && t <= costDelete(N)
                                     && tIsBigO(N, t as R0, linGrowth())       
    {
      t := 0.0; 
      // TODO: implementation with array shift here
    }

  }

  // Complexity proof for Get operation  

  ghost function costGet(N:nat) : R0
  {
    1.0
  }

  lemma lem_costGetBigOconst()
    ensures exists c:R0, n0:nat :: bigOfrom(c, n0, costGet, constGrowth())
  {
    var c, n0 := 1.0, 0;
    forall n:nat | 0 <= n0 <= n
      ensures costGet(n) <= c*constGrowth()(n)
    {
      calc {
           costGet(n);
        == 1.0;
        <= c*1.0;
        == c*constGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, costGet, constGrowth());
  }

  // Complexity proof for Insert operation 

  ghost function costInsert(N:nat) : R0
  {
    N as R0
  }

  lemma lem_costInsertBigOlin() returns (c:R0, n0:nat) 
    ensures bigOfrom(c, n0, costInsert, linGrowth())
  {
    c, n0 := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures costInsert(n) <= c*linGrowth()(n)
    {
      calc {
           costInsert(n);
        == n as R0;
        <= c*n as R0;
        == { lem_expOne(n as R0); }
           c*exp(n as R0, 1.0);
        == c*linGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, costGet, linGrowth());
  }

  // Complexity proof for Delete operation  

  ghost function costDelete(N:nat) : R0 
  // TODO

}