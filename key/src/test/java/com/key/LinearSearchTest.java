package com.key;

import org.junit.jupiter.api.Test;

public class LinearSearchTest {

  @Test
  public void shouldFindKeyAtIndex5() {
    int[] elems = {1, 2, 7, 3, 9, 12, 54, 87, 47, 15};
    int key = 12;
    int index = LinearSearch.linearSearch(elems, key);
    assert(index == 5);
  }

  @Test
  public void shouldNotFindKey() {
    int[] elems = {1, 2, 7, 3, 9, 12, 54, 87, 47, 15};
    int key = 122;
    int index = LinearSearch.linearSearch(elems, key);
    assert(index == -1);
  }

  @Test
  public void shouldNotFindKeyForEmptyArray() {
    int[] elems = {};
    int key = 122;
    int index = LinearSearch.linearSearch(elems, key);
    assert(index == -1);
  }
}
