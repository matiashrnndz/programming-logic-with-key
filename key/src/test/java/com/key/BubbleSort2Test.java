package com.key;

import org.junit.jupiter.api.Test;

public class BubbleSort2Test {

  private BubbleSort2 obj = new BubbleSort2();

  @Test
  public void sortedWith0Elements() {
    int[] elems = {};
    obj.arr = elems;
    obj.bubbleSort2();
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
    obj.bubbleSort2();
    assert(
      obj.arr[0] == expected[0]
    );
  }

  @Test
  public void sortedWith2Elements() {
    int[] elems = {15, 2};
    int[] expected = {2, 15};
    obj.arr = elems;
    obj.bubbleSort2();
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
    obj.bubbleSort2();
    assert(
      obj.arr[0] == expected[0] &&
      obj.arr[1] == expected[1] &&
      obj.arr[2] == expected[2]
    );
  }

  @Test
  public void sorted() {
    int[] elems = {9, 8, 7, 6, 5};
    int[] expected = {5, 6, 7, 8, 9};
    obj.arr = elems;
    obj.bubbleSort2();
    assert(
      obj.arr[0] == expected[0] &&
      obj.arr[1] == expected[1] &&
      obj.arr[2] == expected[2] &&
      obj.arr[3] == expected[3] &&
      obj.arr[4] == expected[4]
    );
  }
}
