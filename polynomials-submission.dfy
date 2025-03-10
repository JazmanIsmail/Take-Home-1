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

// RE-EXAMINE
lemma PolyvalPrefix(a: seq<int>, x: int, i: nat)
  requires i < |a|
  ensures polyval(a[..i+1], x) == polyval(a[..i], x) + a[i] * pow(x, i)

lemma PowerTrue(x: int, i: nat)
    ensures pow(x, i+1) == pow(x, i) * x 
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
        // RE-EXAMINE
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
    // RE-EXAMINE
    // assert r + a[i] * power_x == polyval(a[..i+1], x);
    PolyvalPrefix(a, x, i);
    r := r + a[i] * power_x;
    // PowerTrue(power_x,i);
    // assert power_x == pow(x, i);
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
    {
        r := a[i] + x * r;
        i := i - 1;
    }
}
// END-TODO(HornerPoly)
