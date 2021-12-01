package com.key;

import org.junit.jupiter.api.Test;

public class InsertionSortTest {
  
  @Test
  public void sorted() {
    int[] elems = {15, 7, 2, 12, 1};
    int[] expected = {1, 2, 7, 12, 15};
    InsertionSort is = new InsertionSort();
    is.a = elems;
    is.insertionSort();
    assert(
      is.a[0] == expected[0] &&
      is.a[1] == expected[1] &&
      is.a[2] == expected[2] &&
      is.a[3] == expected[3] &&
      is.a[4] == expected[4]
    );
  }

  @Test
  public void sortedWithSameElems() {
    int[] elems = {15, 7, 2, 12, 7};
    int[] expected = {2, 7, 7, 12, 15};
    InsertionSort is = new InsertionSort();
    is.a = elems;
    is.insertionSort();
    assert(
      is.a[0] == expected[0] &&
      is.a[1] == expected[1] &&
      is.a[2] == expected[2] &&
      is.a[3] == expected[3] &&
      is.a[4] == expected[4]
    );
  }
}
