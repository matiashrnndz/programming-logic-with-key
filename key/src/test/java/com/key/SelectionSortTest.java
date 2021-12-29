package com.key;

import org.junit.jupiter.api.Test;

public class SelectionSortTest {

  private SelectionSort obj = new SelectionSort();

  @Test
  public void sortedWith0Elements() {
    int[] elems = {};
    obj.arr = elems;
    obj.selectionSort();
    assert(
      (obj.arr != null) &&
      (obj.arr.length == 0)
    );
  }

  @Test
  public void sortedWith1Element() {
    int[] elems = {15};
    int[] expected = {15};
    obj.arr = elems;
    obj.selectionSort();
    assert(
      obj.arr[0] == expected[0]
    );
  }

  @Test
  public void sortedWith2Elements() {
    int[] elems = {15, 2};
    int[] expected = {2, 15};
    obj.arr = elems;
    obj.selectionSort();
    assert(
      obj.arr[0] == expected[0] &&
      obj.arr[1] == expected[1]
    );
  }

  @Test
  public void sortedWith3Elements() {
    int[] elems = {15, 2, 14};
    int[] expected = {2, 14, 15};
    obj.arr = elems;
    obj.selectionSort();
    assert(
      obj.arr[0] == expected[0] &&
      obj.arr[1] == expected[1] &&
      obj.arr[2] == expected[2]
    );
  }
}
