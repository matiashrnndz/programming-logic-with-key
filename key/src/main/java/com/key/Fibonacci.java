package com.key;

public class Fibonacci {
  
  /*@ public normal_behavior
    @ requires n != null && 0 <= n && n <= 10;
    @ ensures \result == fib(n);
    @ assignable \strictly_nothing;
    @*/
  public int fibonacci(int n) {
    int a = 0;
    int b = 1;
    int i = 0;
    /*@ loop_invariant 0 <= i && i <= n;
      @ loop_invariant a == fib(i);
      @ loop_invariant b == fib(i+1);
      @ assignable \strictly_nothing;
      @ decreases n - i;
      @*/
    while (i < n) {
      int temp = b;
      b = a + b;
      a = temp;
      i++;
    }
    return a;
  }

  public int fib(int n) {
    if (n == 0) {
      return 0;
    } else if (n == 1) {
      return 1;
    } else {
      return fib(n-1) + fib(n-2);
    }
  }
}
