package com.key;

import org.junit.jupiter.api.Test;

public class BubbleSortTest {

  private BubbleSort alg = new BubbleSort();

  @Test
  public void sortedWith0Elements() {
    int[] elems = {};
    alg.arr = elems;
    alg.bubbleSort();
    assert(
      (alg.arr != null) &&
      (alg.arr.length == 0)
    );
  }

  @Test
  public void sortedWith1Element() {
    int[] elems = {15};
    int[] expected = {15};
    alg.arr = elems;
    alg.bubbleSort();
    assert(
      alg.arr[0] == expected[0]
    );
  }

  @Test
  public void sortedWith2Elements() {
    int[] elems = {15, 2};
    int[] expected = {2, 15};
    alg.arr = elems;
    alg.bubbleSort();
    assert(
      alg.arr[0] == expected[0] &&
      alg.arr[1] == expected[1]
    );
  }

  @Test
  public void sortedWith3Elements() {
    int[] elems = {15, 2, 14};
    int[] expected = {2, 14, 15};
    alg.arr = elems;
    alg.bubbleSort();
    assert(
      alg.arr[0] == expected[0] &&
      alg.arr[1] == expected[1] &&
      alg.arr[2] == expected[2]
    );
  }

  @Test
  public void sorted() {
    int[] elems = {9, 8, 7, 6, 5};
    int[] expected = {5, 6, 7, 8, 9};
    alg.arr = elems;
    alg.bubbleSort();
    assert(
      alg.arr[0] == expected[0] &&
      alg.arr[1] == expected[1] &&
      alg.arr[2] == expected[2] &&
      alg.arr[3] == expected[3] &&
      alg.arr[4] == expected[4]
    );
  }
}
