// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
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
// Give a verifying implementation of log-time exponentiation that follows the
// specification given in `pow`.
// END-TODO(FastExp)

