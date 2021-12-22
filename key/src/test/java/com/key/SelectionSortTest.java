package com.key;

import org.junit.jupiter.api.Test;

public class SelectionSortTest {

  @Test
  public void sortedWith0Elements() {
    int[] elems = {};
    SelectionSort alg = new SelectionSort();
    alg.arr = elems;
    alg.selectionSort();
    assert(
      (alg.arr != null) &&
      (alg.arr.length == 0)
    );
  }

  @Test
  public void sortedWith1Element() {
    int[] elems = {15};
    int[] expected = {15};
    SelectionSort alg = new SelectionSort();
    alg.arr = elems;
    alg.selectionSort();
    assert(
      alg.arr[0] == expected[0]
    );
  }

  @Test
  public void sortedWith2Elements() {
    int[] elems = {15, 2};
    int[] expected = {2, 15};
    SelectionSort alg = new SelectionSort();
    alg.arr = elems;
    alg.selectionSort();
    assert(
      alg.arr[0] == expected[0] &&
      alg.arr[1] == expected[1]
    );
  }

  @Test
  public void sortedWith3Elements() {
    int[] elems = {15, 2, 14};
    int[] expected = {2, 14, 15};
    SelectionSort alg = new SelectionSort();
    alg.arr = elems;
    alg.selectionSort();
    assert(
      alg.arr[0] == expected[0] &&
      alg.arr[1] == expected[1] &&
      alg.arr[2] == expected[2]
    );
  }
}
