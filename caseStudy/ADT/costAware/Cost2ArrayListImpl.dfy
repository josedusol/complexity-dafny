include "../../../theory/math/ExpReal.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity/Asymptotics.dfy"
include "./Cost2ArrayList.dfy"
//include "./LemArrayList.dfy"
//include "./CostArrayList.dfy"

/******************************************************************************
  Implementation of ArrayList ADT
******************************************************************************/

module Cost2ArrayListImpl refines Cost2ArrayList {

  class Cost2ArrayListImpl<T(0)> extends Cost2ArrayList<T> {

    var arr:array<T>
    var nElems:nat

    constructor(capacity:nat)
      // Pre:
      requires capacity > 0
      // Post:      
      ensures Valid()
      ensures arr.Length == capacity
      ensures Size() == 0
    {
      arr := new T[capacity];   
      nElems := 0; 
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
      nElems
    }

    // Returns the capacity of the list
    function Capacity(): nat
      reads this, Repr()
      // Pre:
      requires Valid()  
    {
      arr.Length
    }         

    // Returns the element at position i in the list
    function Get(i:nat): (ret: (T, ghost R0))    
      reads this, Repr()
      // Pre:
      requires Valid()
      requires 0 <= i < Size() 
      // Complexity:
      //ensures var t := ret.1; t <= Tget(Size())
      //ensures var t := ret.1; tIsBigOh(Size(), t as R0, constGrowth())      
    {
      //lem_Get_TgetBigOconst();
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
      && 0 <= nElems <= arr.Length
      && 0 < arr.Length
      && this in Repr() 
      && arr  in Repr()
    }    

    /******************************************************************************
      Update operations
    ******************************************************************************/
    
    //Experiment with cost objects

    // Inserts element x at position k in the list
    method Insert(k:nat, x:T) returns (ghost c:Cost2<ArrayOp<T>, State<T>>)
      modifies this, Repr()  
      // Pre:
      requires Valid() && ValidModel()
      requires 0 <= k <= Size()
      requires !IsFull()
      // Post:
      ensures  Valid() && ValidModel() && fresh(Repr() - old(Repr()))
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < k           ==> Get(j).0 == old(Get(j).0)    // [0, k)           is unchanged  
      ensures  forall j :: k < j <= old(Size()) ==> Get(j).0 == old(Get(j-1).0)  // [k, old(Size())) is right shifted 
      ensures  Get(k).0 == x                                                     // xs[k] == x
      // Cost:
      ensures  c.OpsValid(old(elems))            
      ensures  c.ApplyOps(old(elems)) == elems    // Even this does not prevent under-reporting of cost.
      ensures  c.Count() == old(Size()) - k + 1
    { 
      c := new ArrayInsertCost(); assert c.Count() == 0;
      var N := Size(); // == nElems 

      // Update model
      assert nElems == |elems|; 
      assert (forall i :: 0 <= i < nElems ==> arr[i] == elems[i]);
      elems := elems[..k] + [x] + elems[k..];
      
      // Update array:
      // 1. Shift [k, N) to the right
      for i := N downto k
        modifies arr, c
        invariant N < arr.Length
        invariant arr[..i]      == old(arr[..i])   // [0, i) is unchanged  
        invariant arr[i+1..N+1] == old(arr[i..N])  // (i, N) is right shifted        
        invariant c.Count() == N - i
      {
        arr[i+1] := arr[i];              // shift right
        assert arr[i+1] == old(arr[i]);
        c.Log(Write(i+1, arr[i]), 1); //t := t + 1.0;
      }
      assert arr[..k] == old(arr[..k]) == elems[..k];          // [0, k) is unchanged
      assert arr[k+1..N+1] == old(arr[k..N]) == elems[k+1..];  // [k, N] is right shifted 

      // 2. Insert x at position k
      arr[k] := x;
      c.Log(Write(k, x), 1);  //t := t + 1.0;
     
      // Update number of elements
      nElems := nElems + 1;
      assert forall j :: 0 <= j < |elems| ==> arr[j] == elems[j];

      assert c.Count() == N - k + 1; 
    }   

    method Append(x:T) returns (ghost c:Cost2<ArrayOp<T>, State<T>>)  
      modifies this, Repr()    
      // Pre:
      requires Valid() && ValidModel()
      requires !IsFull()
      // Post:
      ensures  Valid() && ValidModel()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < old(Size()) ==> Get(j).0 == old(Get(j).0)    // [0, old(Size())) is unchanged  
      ensures  Get(old(Size())).0 == x  
      // Complexity:
      //ensures  var N := old(Size()); c.Count() == AppendCost<T>.Cost(N)    
  //  { 
      // var N := Size(); 
      // c := new AppendCost(arr, N, x); 
      // var c' := Insert_CostTest(N, x);
      // c.t := c'.t;
      // assert c.Count() == InsertCost<T>.Cost(N, N) == 1;     
   // }    

  }

}