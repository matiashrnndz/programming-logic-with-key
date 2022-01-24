package com.key;

public class BinarySearch {
  
  /*@ public normal_behavior
    @ requires (\forall int a, b;
    @                   0 <= a && a <= b && b < arr.length;
    @                   arr[a] <= arr[b]);
    @ ensures \result >= 0 ==>
    @           \result < arr.length && arr[\result] == key;
    @ ensures \result == -1 ==>
    @           (\forall  int k;
    @                     0 <= k && k < arr.length;
    @                     arr[k] != key);
    @ assignable \strictly_nothing;
    @*/
  public int binarySearch(int[] arr, int key) {
    int low = 0, high = arr.length;
    /*@ loop_invariant 0 <= low && low <= high && high <= arr.length;
      @ loop_invariant (\forall int k;
      @                         0 <= k && k < low;
      @                         arr[k] != key);
      @ loop_invariant (\forall int k;
      @                         high <= k && k < arr.length;
      @                         arr[k] != key);
      @ assignable \strictly_nothing;
      @ decreases high - low;
      @*/
    while (low < high) {
      int mid = (low + high) / 2;
      if (key < arr[mid]) {
        high = mid;
      } else if (key > arr[mid]) {
        low = mid + 1;
      } else {
        return mid;
      }
    }
    return -1;
  }
}
