// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 69
// Jazman Mohamad Ismail: 1923072
// Arhan Chhabra: 1940198
//
// Show us what you're made of!
//
// END-TODO(Name)

ghost function polyval(a: seq<int>, x: int): int
{
    if |a| == 0
    then
        0
    else
        var d := |a|-1; //degree, highest exponent of x
        polyval(a[..d], x) +a[d] * pow(x, d)
}


function pow(x: int, n: nat) : int
{
    if n == 0
    then
        1
    else
        x * pow(x, n - 1)
}


// BEGIN-TODO(Optional)

lemma PolyvalPrefix(a: seq<int>, x: int, i: nat)
  requires i < |a|
  ensures polyval(a[..i+1], x) == polyval(a[..i], x) + a[i] * pow(x, i)
  {
    if (i == 0) { // Base case
        calc {
            polyval(a[..0+1], x);
            ==
            polyval(a[..1], x);
            == // apply def. of polyval
            polyval(a[..1][..0], x) + a[..1][0] * pow(x, 0);
            == 
            0 + a[0] * pow(x, 0);
            == // pow(x,0) == 1 as established
            0 + a[0] * 1;
            ==
            a[0];
        }
    } else { // Step case
        // Asserting explicit slicing rule to help dafny verify the below calculations
        assert a[..i+1] == a[..i] + [a[i]];
        calc {
            polyval(a[..i+1], x);
            == // Use def.
            polyval(a[..i+1][..i], x) + a[..i+1][i] * pow(x, i);
            == // Simplfy
            polyval(a[..i], x) + a[i] * pow(x, i);
        }
    }
}

lemma PowerTrue(x: int, i: nat)
    ensures pow(x, i+1) == pow(x, i) * x 
    {
        if (i == 0) { // Base case
            assert pow(x,0) == 1;
        } else {
            calc {
                pow(x,i+1);
                == // Def. of pow
                x * pow(x, (i+1) - 1);
                == // Simplification and thus result
                x * pow(x, i);
            }
        }
    }
// Define an additional Horner lemma to help with Dafny verification
lemma HornerAdditionalHelp(b: seq<int>, x: int)
  requires |b| > 0
  ensures polyval(b, x) == b[0] + if |b| == 1 then 0 else x * polyval(b[1..], x)
{
  if |b| == 1 { // Base case
    calc { // Applying definition of polyval and further simplicification
      polyval(b, x);
      ==
      polyval(b[..0], x) + b[0] * pow(x, 0);
      == 
      0 + b[0] * 1;
      == 
      b[0];
    }
  } else { // Step case
    var n := |b|;
    calc {
      polyval(b, x);
      == 
      polyval(b[..n-1], x) + b[n-1] * pow(x, n-1); // Apply def.
      ==
      b[0] + x * polyval(b[1..n-1], x) + b[n-1] * pow(x, n-1); // Expand
    }
    // Asserts to Dafny about rules of slicing sequences and the two ways are equivalent
    // Dafny cannot verify without this assertion
    assert b[1..][..n-2] == b[1..n-1];
    calc {
      b[0] + x * (polyval(b[1..n-1], x) + b[n-1] * pow(x, n-2)); // Simplify
      ==
      b[0] + x * polyval(b[1..], x);
    }
  }
}


lemma HornerHelp(a: seq<int>, x: int, i: nat)
    requires i < |a|
    ensures polyval(a[i..], x) == a[i] + x * polyval(a[i+1..], x)
{
  var b := a[i..];
  // Uses the additional Horner lemma to prove HornerHelp
  HornerAdditionalHelp(b, x);
}
// END-TODO(Optional)


method polySimple(a: seq<int>, x: int) returns (r: int)
    ensures r == polyval(a, x)
// BEGIN-TODO(NaivePoly)
{
    r := 0;
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant r == polyval(a[..i], x)
        invariant a[..|a|] == a
    {
        // assert a[..i+1] == a[..i] + [a[i]];
        PolyvalPrefix(a, x, i);
        r := r + a[i] * pow(x, i);
        i := i + 1;
    }
}
// END-TODO(NaivePoly)


method polyPowerCache(a: seq<int>, x: int) returns (r: int)
    ensures r == polyval(a, x)
// BEGIN-TODO(CachePoly)
{
  r := 0;
  var power_x := 1;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant power_x == pow(x, i)
    invariant r == polyval(a[..i], x)
    invariant a[..|a|] == a
  {
    PolyvalPrefix(a, x, i);
    r := r + a[i] * power_x;
    power_x := power_x * x;
    i := i + 1;
  }
}
// END-TODO(CachePoly)


method Horner(a: seq<int>, x: int) returns (r: int)
    ensures r == polyval(a, x)
// BEGIN-TODO(HornerPoly)
{
    r := 0;
    var i := |a| - 1;
    while i >= 0
        invariant -1 <= i < |a|
        invariant r == polyval(a[i+1..], x)
        decreases i
    {
        HornerHelp(a, x, i);
        if (i >= 0) {
            r := a[i] + x * r;
            i := i - 1;
        }
    }
}
// END-TODO(HornerPoly)
