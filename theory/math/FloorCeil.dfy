
/**************************************************************************
  Floors and ceilings
**************************************************************************/

module FloorCeil {
  
  // floor(x) <= x < floor(x)+1
  ghost function {:axiom} floor(x:real) : int
    ensures floor(x) as real <= x
    ensures x < (floor(x) as real) + 1.0

  // ceil(x)-1 < x <= ceil(x)
  ghost function {:axiom} ceil(x:real) : int
    ensures (ceil(x) as real) - 1.0 < x
    ensures x <= ceil(x) as real

  ghost function ceil2(x:real, n:int) : int
  { 
    if x == floor(x) as real 
    then floor(x) 
    else floor(x) + 1 
  }

  ghost function ceil3(x:real, n:int) : int
  { 
     -floor(-x)
  }  

  lemma {:axiom} lem_ceilxLEQnIFFxLEQn(x:real, n:int)
    ensures ceil(x) <= n <==> x <= n as real
    
}