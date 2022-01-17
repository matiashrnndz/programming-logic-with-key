package com.key;

import org.junit.jupiter.api.Test;

public class FibonacciTest {

  private Fibonacci obj = new Fibonacci();

  @Test
  public void fib0() {
    int expected = 1;
    int result = obj.fib_iterative(0);
    assert(result == expected);
  }

  @Test
  public void fib1() {
    int expected = 1;
    int result = obj.fib_iterative(1);
    assert(result == expected);
  }

  @Test
  public void fib2() {
    int expected = 2;
    int result = obj.fib_iterative(2);
    assert(result == expected);
  }

  @Test
  public void fib3() {
    int expected = 3;
    int result = obj.fib_iterative(3);
    assert(result == expected);
  }

  @Test
  public void fib4() {
    int expected = 5;
    int result = obj.fib_iterative(4);
    assert(result == expected);
  }

  @Test
  public void fib5() {
    int expected = 8;
    int result = obj.fib_iterative(5);
    assert(result == expected);
  }

  @Test
  public void fib6() {
    int expected = 13;
    int result = obj.fib_iterative(6);
    assert(result == expected);
  }

  @Test
  public void fib7() {
    int expected = 21;
    int result = obj.fib_iterative(7);
    assert(result == expected);
  }

  @Test
  public void fib8() {
    int expected = 34;
    int result = obj.fib_iterative(8);
    assert(result == expected);
  }

  @Test
  public void fib9() {
    int expected = 55;
    int result = obj.fib_iterative(9);
    assert(result == expected);
  }

  @Test
  public void fib10() {
    int expected = 89;
    int result = obj.fib_iterative(10);
    assert(result == expected);
  }
}
