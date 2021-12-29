package com.key;

import org.junit.jupiter.api.Test;

public class InsertionSortTest {
  
  private InsertionSort obj = new InsertionSort();

  @Test
  public void sorted() {
    int[] elems = {15, 7, 2, 12, 1};
    int[] expected = {1, 2, 7, 12, 15};
    obj.arr = elems;
    obj.insertionSort();
    assert(
      obj.arr[0] == expected[0] &&
      obj.arr[1] == expected[1] &&
      obj.arr[2] == expected[2] &&
      obj.arr[3] == expected[3] &&
      obj.arr[4] == expected[4]
    );
  }

  @Test
  public void sortedWithSameElems() {
    int[] elems = {15, 7, 2, 12, 7};
    int[] expected = {2, 7, 7, 12, 15};
    obj.arr = elems;
    obj.insertionSort();
    assert(
      obj.arr[0] == expected[0] &&
      obj.arr[1] == expected[1] &&
      obj.arr[2] == expected[2] &&
      obj.arr[3] == expected[3] &&
      obj.arr[4] == expected[4]
    );
  }
}
