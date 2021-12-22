package com.key;

import org.junit.jupiter.api.Test;

public class InsertionSortTest {
  
  @Test
  public void sorted() {
    int[] elems = {15, 7, 2, 12, 1};
    int[] expected = {1, 2, 7, 12, 15};
    InsertionSort is = new InsertionSort();
    is.arr = elems;
    is.insertionSort();
    assert(
      is.arr[0] == expected[0] &&
      is.arr[1] == expected[1] &&
      is.arr[2] == expected[2] &&
      is.arr[3] == expected[3] &&
      is.arr[4] == expected[4]
    );
  }

  @Test
  public void sortedWithSameElems() {
    int[] elems = {15, 7, 2, 12, 7};
    int[] expected = {2, 7, 7, 12, 15};
    InsertionSort is = new InsertionSort();
    is.arr = elems;
    is.insertionSort();
    assert(
      is.arr[0] == expected[0] &&
      is.arr[1] == expected[1] &&
      is.arr[2] == expected[2] &&
      is.arr[3] == expected[3] &&
      is.arr[4] == expected[4]
    );
  }
}
