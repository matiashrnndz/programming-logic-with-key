package key;

public class Fibonacci {

  /*@ model_behavior
    @ requires n >= 0;
    @ model int fib(int n) {
    @   return (n == 0 || n == 1) ? 1 : fib(n-1) + fib(n-2);
    @ }
    @*/

  /*@ public normal_behavior
    @ requires n >= 0;
    @ ensures \result == fib(n);
    @ decreases n;
    @*/
  public int fib_iterative(int n) {
    int a = 1;
    int b = 1;
    int i = 0;
    /*@ loop_invariant 0 <= i && i <= n;
      @ loop_invariant a == fib(i);
      @ loop_invariant b == fib(i+1);
      @ assignable \strictly_nothing;
      @ decreases n - i;
      @*/
    while (i != n) {
      int olda = a;
      a = b;
      b = olda + b;
      i++;
    }
    return a;
  }
}
