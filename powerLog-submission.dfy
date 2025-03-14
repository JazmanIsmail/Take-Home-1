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

// Adapt one of the lemmas from textbook
lemma {:induction false} ExpSquareBase(b: nat, n: nat)
  ensures pow(b * b, n) == pow(b, 2 * n)
  {
    if n == 0 { // Base case
      calc {
      pow(b * b, 0); // Def.
      ==
      1;
      ==
      pow(b, 0); // Re-apply def.
      ==
      pow(b, 2 * 0); // Re-write prev. expression
    }
  } else { // Step case
    ExpSquareBase(b, n - 1); // Apply IH
    calc {
      pow(b * b, n);
      ==
      (b * b) * pow(b * b, n - 1); // Apply def.
      ==
      (b * b) * pow(b, 2 * (n - 1)); // Equiv.
      == 
      pow(b, 2 * n); // Re-write equiv.
    }
  }
  }

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
      ExpSquareBase(a, n/2);
      a := a * a;
      n := n / 2;
    }
  }
}
// END-TODO(FastExp)

