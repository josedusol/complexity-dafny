include "../../../../theory/math/ExpReal.dfy"
include "../../../../theory/math/TypeR0.dfy"
include "../../../../theory/ComplexityR0.dfy"
include "../List.dfy"
include "./LemArrayList.dfy"
//include "./CostArrayList.dfy"

/******************************************************************************
  Array implementation of a List
******************************************************************************/

module ArrayList refines List {

  import opened LemArrayList
  
  // Refine input type for each relevant operation
  type InsertIn<T> = (array<T>, nat, nat, T)    
  type AppendIn<T> = (array<T>, nat, T)   
  type OkIn<T> = (array<T>, nat)   

  class ArrayList<T(0)> extends List<T> {

    var arr:array<T>
    var nElems:nat
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
      nElems := 0; 
      elems := [];
    }   

    // default constructor
    static method Create<T(0)>() returns (obj:ArrayList)
      ensures obj.arr.Length == 1
    {
      obj := new ArrayList<T>(1);
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
      ensures var t := ret.1; t <= Tget(Size())
      ensures var t := ret.1; tIsBigO(Size(), t as R0, constGrowth())      
    {
      lem_Get_TgetBigOconst();
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
      // The array and its ghost counterpart are aligned
      && nElems == |elems| 
      && (forall i :: 0 <= i < nElems ==> arr[i] == elems[i])
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
      requires !IsFull()
      // Post:
      ensures  Valid() && fresh(Repr() - old(Repr()))
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < k           ==> Get(j).0 == old(Get(j).0)    // [0, k)           is unchanged  
      ensures  forall j :: k < j <= old(Size()) ==> Get(j).0 == old(Get(j-1).0)  // [k, old(Size())) is right shifted 
      ensures  Get(k).0 == x                                                     // xs[k] == x
      // Complexity:
      ensures  var N := old(Size()); && t == Tinsert(N,k)
                                     && tIsBigO(N, t as R0, linGrowth())                             
    {
      var N := Size();
      t := 0.0;

      // Update model
      elems := elems[..k] + [x] + elems[k..];
      
      // Update array:
      // 1. Shift [k, N) to the right
      for i := N downto k
        modifies arr
        invariant N < arr.Length
        invariant arr[..i]      == old(arr[..i])   // [0, i) is unchanged  
        invariant arr[i+1..N+1] == old(arr[i..N])  // (i, N) is right shifted        
        invariant t == (N - i) as R0    
      {
        arr[i+1] := arr[i]; // shift right
        assert arr[i+1] == old(arr[i]);
        t := t + 1.0;
      }
      assert arr[..k] == old(arr[..k]) == elems[..k];          // [0, k) is unchanged
      assert arr[k+1..N+1] == old(arr[k..N]) == elems[k+1..];  // [k, N] is right shifted 

      // 2. Insert x at position k
      arr[k] := x;
      t := t + 1.0;

      // Update number of elements
      nElems := nElems + 1;
      assert forall j :: 0 <= j < |elems| ==> arr[j] == elems[j];

      assert t == (N - k + 1) as R0 == Tinsert(N, k) 
               <= (N + 1) as R0     == Tinsert2(N);
      assert Tinsert2 in O(linGrowth()) by { var c, n0 := lem_Insert_Tinsert2BigOlin(); }      
    }
                                              
    // Appends element x in the list
    method Append(x:T) returns (ghost t:R0)
      modifies this, Repr()    
      // Pre:
      requires Valid()
      requires !IsFull()
      // Post:
      ensures  Valid()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < old(Size()) ==> Get(j).0 == old(Get(j).0)    // [0, old(Size())) is unchanged  
      ensures  Get(old(Size())).0 == x  
      // Complexity:
      ensures  var N := old(Size()); && t == Tappend(N) 
                                     && tIsBigO(N, t as R0, constGrowth())      
    {
      var N := Size();
      t := Insert(N, x);
      assert t == Tinsert(N, N) == 1 as R0; 
      assert Tappend in O(constGrowth()) by { var c, n0 := lem_Append_TappendBigOconst(); }      
    }

    // Deletes element at position k in the list
    method {:axiom} Delete(k:nat) returns (ghost t:R0)
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
      ensures  var N := old(Size()); && t <= Tdelete(N)
                                     && tIsBigO(N, t as R0, linGrowth())       
      // TODO: implementation with array shift here

    /******************************************************************************
      Experiment with cost objects
    ******************************************************************************/

    // Inserts element x at position k in the list
    method Insert_CostTest(k:nat, x:T) returns (ghost c:Cost<InsertIn<T>>)
      modifies this, Repr()    
      // Pre:
      requires Valid()
      requires 0 <= k <= Size()
      requires !IsFull()
      // Post:
      ensures  Valid() && fresh(Repr() - old(Repr()))
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < k           ==> Get(j).0 == old(Get(j).0)    // [0, k)           is unchanged  
      ensures  forall j :: k < j <= old(Size()) ==> Get(j).0 == old(Get(j-1).0)  // [k, old(Size())) is right shifted 
      ensures  Get(k).0 == x                                                     // xs[k] == x
      // Complexity:
      ensures  var N := old(Size()); c.Count() == InsertCost<T>.Cost(N, k)
    { 
      c := new InsertCost(arr, nElems, k, x); 
      var N := Size(); // == nElems

      // Update model
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
        c.Inc(); //t := t + 1.0;
      }
      assert arr[..k] == old(arr[..k]) == elems[..k];          // [0, k) is unchanged
      assert arr[k+1..N+1] == old(arr[k..N]) == elems[k+1..];  // [k, N] is right shifted 

      // 2. Insert x at position k
      arr[k] := x;
      c.Inc();  //t := t + 1.0;
     
      // Update number of elements
      nElems := nElems + 1;
      assert forall j :: 0 <= j < |elems| ==> arr[j] == elems[j];

      assert c.Count() == N - k + 1 == InsertCost<T>.Cost(c.Size(), k); 
    }   

    method Append_CostTest(x:T) returns (ghost c:Cost<AppendIn<T>>)  
      modifies this, Repr()    
      // Pre:
      requires Valid()
      requires !IsFull()
      // Post:
      ensures  Valid()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < old(Size()) ==> Get(j).0 == old(Get(j).0)    // [0, old(Size())) is unchanged  
      ensures  Get(old(Size())).0 == x  
      // Complexity:
      ensures  var N := old(Size()); c.Count() == AppendCost<T>.Cost(N)    
    { 
      var N := Size(); 
      c := new AppendCost(arr, N, x); 
      var c' := Insert_CostTest(N, x);
      c.t := c'.t;
      assert c.Count() == InsertCost<T>.Cost(N, N) == 1;     
    }    

    method OK_CostTest() returns (ghost c:Cost<OkIn<T>>)  
      modifies this, Repr()     
      // Pre:
      requires Valid()
      // Post:
      ensures  Valid()     
      ensures  tIsBigO(c.Size(), c.Count() as R0, linGrowth())   
    {
      var N := Size(); 
      c := new OkCost(arr, N);
      
      c.t := 2*N;  

      assert c.Count() == 2*N <= 2*arr.Length == OkCost<T>.Cost(arr.Length);
      assert (n => OkCost<T>.Cost(n) as R0) in O(linGrowth()) 
        by { var c, n0 := lem_OK_BigOlin<T>(); }      
    }

  }

  class InsertCost<T> extends Cost<InsertIn<T>> {
    ghost constructor(arr:array<T>, nElems:nat, k:nat, x_:T) 
      requires k <= nElems
      ensures Count() == 0
      ensures Input() == (arr, nElems, k, x_) 
    {
      t, x := 0, (arr, nElems, k, x_);
    }
   
    ghost function Size(): nat
      reads this
    { 
      x.1 
    }

    ghost static function Cost(N:nat, k:nat) : nat
      requires N >= k
    {
      N - k + 1
    }

  }

  class AppendCost<T> extends Cost<AppendIn<T>> {
    ghost constructor(arr:array<T>, nElems:nat, x_:T)
      ensures Count() == 0
      ensures Input() == (arr, nElems, x_) 
    {
      t, x := 0, (arr, nElems, x_);
    }
  
    ghost function Size(): nat
      reads this
    { 
      x.1 
    }

    ghost static function Cost(N:nat) : nat
    {
      1
    }
  }

  class OkCost<T> extends Cost<OkIn<T>> {
    ghost constructor(arr:array<T>, nElems:nat)
      ensures Count() == 0
      ensures Input() == (arr, nElems) 
    {
      t, x := 0, (arr, nElems);
    }
  
    ghost function Size(): nat
      reads this
    { 
      x.0.Length 
    }

    ghost static function Cost(N:nat) : nat
    {
      2*N
    }
  }

  lemma lem_OK_BigOlin<T>() returns (c:R0, n0:nat) 
    ensures c > 0.0 && bigOfrom(c, n0, (n => OkCost<T>.Cost(n) as R0), linGrowth())
  {
    c, n0 := 2.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures (n => OkCost<T>.Cost(n) as R0)(n) <= c*linGrowth()(n)
    {
      calc {
           (n => OkCost<T>.Cost(n) as R0)(n);
        == (2*n)  as R0;
        <= c*n as R0;
        == { lem_expOne(n as R0); }
           c*exp(n as R0, 1.0);
        == c*linGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, (n => OkCost<T>.Cost(n) as R0), linGrowth());
  }    

}