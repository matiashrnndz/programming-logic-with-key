package com.key;

public class BinarySearch {
  
  /*@ public normal_behavior
    @ requires (\forall int i, j; 0 <= i && i <= j && j < a.length; a[i] <= a[j]);
    @ ensures \result >= 0 ==> \result < a.length && a[\result] == key;
    @ ensures \result == -1 ==> (\forall int i; 0 <= i && i < a.length; a[i] != key);
    @ assignable \strictly_nothing;
    @*/
  public static int binarySearch(int[] a, int key) {
    int low = 0, high = a.length;
    /*@ loop_invariant 0 <= low && low <= high && high <= a.length;
      @ loop_invariant (\forall int k; 0 <= k && k < low; a[k] != key);
      @ loop_invariant (\forall int k; high <= k && k < a.length; a[k] != key);
      @ assignable \strictly_nothing;
      @ decreases high - low;
      @*/
    while (low < high) {
      int mid = (low + high) / 2;
      if (key < a[mid]) {
        high = mid;
      } else if (key > a[mid]) {
        low = mid + 1;
      } else {
        return mid;
      }
    }
    return -1;
  }
}
