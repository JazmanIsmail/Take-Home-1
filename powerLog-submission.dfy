// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 69
// Jazman Mohamad Ismail: 1923072
// Arhan Chhabra: 1940198
//
// Show us what you're made of!
//
// END-TODO(Name)

ghost function pow(x: nat, n: nat): nat
{
  if n == 0 then 1 else x * pow(x, n - 1)
}

// BEGIN-TODO(Optional)
// Optionally add your lemmas and helper functions here.
// END-TODO(Optional)

method FastExp(X: nat, N: nat) returns (y: nat)
  ensures y == pow(X, N)
// BEGIN-TODO(FastExp)
{
  var a := X;
  var n := N;
  y := 1;
  while (n > 0)
    invariant y * pow(a, n) == pow(X, N)
    decreases n;
  {
    if (n % 2 == 1) {
      y := y * a;
    }
    a := a * a;
    n := n / 2;
  }
}
// END-TODO(FastExp)

