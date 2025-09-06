
/******************************************************************************
  Floors and ceilings
******************************************************************************/

module FloorCeil {
  
  // floor(x) <= x < floor(x)+1
  ghost function {:axiom} floor(x:real) : int
    ensures floor(x) as real <= x
    ensures x < (floor(x) as real) + 1.0

  // ceil(x)-1 < x <= ceil(x)
  ghost function {:axiom} ceil(x:real) : int
    ensures (ceil(x) as real) - 1.0 < x
    ensures x <= ceil(x) as real

  // alt. def. of ceil
  ghost function ceil2(x:real, n:int) : int
  { 
    if x == floor(x) as real 
    then floor(x) 
    else floor(x) + 1 
  }

  // alt. def. of ceil
  ghost function ceil3(x:real, n:int) : int
  { 
     -floor(-x)
  }  

  // ceil(x) <= n <==> x <= n
  lemma {:axiom} lem_ceilxLEQnIFFxLEQn(x:real, n:int)
    ensures ceil(x) <= n <==> x <= n as real

  // floor(x) <= ceil(x)
  lemma lem_floorLEQceil(x:real)
    ensures floor(x) <= ceil(x)
  { }

  // floor(x) + 1 >= ceil(x)
  lemma lem_floorPlus1GEQceil(x:real) 
    ensures floor(x) + 1 >= ceil(x)
  { }

  // x <= y ==> floor(x) <= ceil(y)
  lemma lem_floorCeilMono(x:real, y:real)
    ensures x <= y ==> floor(x) <= ceil(y)
  { }
  
    // x <= y ==> floor(x/d) <= ceil(y/d)
  lemma lem_floorCeilMonoDiv(x:real, y:real, d:real)
    requires d > 0.0
    ensures  x <= y ==> floor(x/d) <= ceil(y/d)
  { }
    
}