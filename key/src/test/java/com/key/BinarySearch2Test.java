package com.key;

import org.junit.jupiter.api.Test;

public class BinarySearch2Test {

  private BinarySearch2 obj = new BinarySearch2();

  @Test
  public void shouldFindKeyAtIndex0() {
    int[] elems = {1, 2, 7, 12, 15, 19};
    int key = 1;
    int index = obj.binarySearch2(elems, key);
    assert(index == 0);
  }

  @Test
  public void shouldFindKeyAtIndex1() {
    int[] elems = {1, 2, 7, 12, 15, 19};
    int key = 2;
    int index = obj.binarySearch2(elems, key);
    assert(index == 1);
  }

  @Test
  public void shouldFindKeyAtIndex2() {
    int[] elems = {1, 2, 7, 12, 15, 19};
    int key = 7;
    int index = obj.binarySearch2(elems, key);
    assert(index == 2);
  }

  @Test
  public void shouldFindKeyAtIndex3() {
    int[] elems = {1, 2, 7, 12, 15, 19};
    int key = 12;
    int index = obj.binarySearch2(elems, key);
    assert(index == 3);
  }

  @Test
  public void shouldFindKeyAtIndex4() {
    int[] elems = {1, 2, 7, 12, 15, 19};
    int key = 15;
    int index = obj.binarySearch2(elems, key);
    assert(index == 4);
  }

  @Test
  public void shouldFindKeyAtIndex5() {
    int[] elems = {1, 2, 7, 12, 15, 19};
    int key = 19;
    int index = obj.binarySearch2(elems, key);
    assert(index == 5);
  }

  @Test
  public void shouldNotFindKey() {
    int[] elems = {1, 2, 7, 12, 15, 19};
    int key = 122;
    int index = obj.binarySearch2(elems, key);
    assert(index == -1);
  }

  @Test
  public void shouldNotFindKeyForEmptyArray() {
    int[] elems = {};
    int key = 122;
    int index = obj.binarySearch2(elems, key);
    assert(index == -1);
  }
}
