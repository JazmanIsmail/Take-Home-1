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

// ghost function Exp(b: nat, n: nat): nat {
//   if n == 0 then 1 else b * Exp(b, n-1)
// }

// method computeExp(b: nat, n: nat): nat {

// }

// Do I need to prove this further though?
// And are these lemmas good enough (just copied from book and replaced exp with pow)
lemma {:induction false} ExpAddExponent(b: nat, m: nat, n: nat)
  ensures pow(b, m + n) == pow(b, m) * pow(b, n)
lemma {:induction false} ExpSquareBase(b: nat, n: nat)
  ensures pow(b * b, n) == pow(b, 2 * n)

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
    // invariant 1 <= y <= N
    decreases n
  {
    // fact about div and mod, for any integer k: k == 2 * (k / 2) + k % 2
    if (n % 2 == 1) {
      y := y * a;
      n := n - 1;
    } else {
      ExpSquareBase(a, n / 2);
      a := a * a;
      n := n / 2;
    }
  }
}
// END-TODO(FastExp)

