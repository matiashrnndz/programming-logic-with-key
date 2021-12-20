package com.key;

public class Fibonacci {

  /*@ model_behavior
    @ requires n >= 0;
    @ model int fib(int n) {
    @   returns (n == 0 || n == 1) ? 1 : fib(n-1) + fib(n-2);
    @ }
    @*/

  /*@ public normal_behavior
    @ requires n >= 0;
    @ ensures \result == fib(n);
    @ decreases n;
    @*/
  public int fib_iterative(int n) {
    int a = 1, b = 1;
    /*@ loop_invariant 0 <= i && i <= n;
      @ loop_invariant a == fib(i);
      @ loop_invariant b == fib(i+1);
      @ assignable \strictly_nothing;
      @ decreases n - i;
      @*/
    for (int i = 0; i < n; i++) {
      int olda = a;
      a = b; b = olda + b;
    }
    return a;
  }
}
