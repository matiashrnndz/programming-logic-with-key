package key;

public class FibonacciRec {

  /*@ model_behavior
    @ requires n >= 0;
    @ model int fib(int n) {
    @   return (n == 0 || n == 1) ? 1 : fib(n-1) + fib(n-2);
    @ }
    @*/

  /*@ public normal_behavior
    @ requires n >= 0;
    @ ensures \result == fib(n);
    @ measured_by n;
    @ assignable \strictly_nothing;
    @*/
  public int fib_recursive(int n) {
    if (n == 0 || n == 1) {
      return 1;
    }
    return fib_recursive(n-2) + fib_recursive(n-1);
  }
}
