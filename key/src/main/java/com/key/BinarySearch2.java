package com.key;

public class BinarySearch2 {
  /*@ public behavior
    @ requires a != null;
    @ requires (\forall int i, j; 0 <= i && j < a.length; i <= j ==> a[i] <= a[j]);
    @ ensures \result >= 0 && \result < a.length ==> a[\result] == key;
    @ ensures \result == -1 ==> (\forall int i; 0 <= i && i < a.length; a[i] != key);
    @ assignable \nothing;
    @*/
  public static int binarySearch(int[] a, int key) {
    int low = 0;
    int high = a.length - 1;
    /*@ loop_invariant 0 <= low && low <= high && high < a.length;
      @ loop_invariant (\forall int k; 0 <= k && k < a.length && a[k] == key; low <= k && k <= high);
      @ assignable \nothing;
      @ decreases high - low;
      @*/
    while (low <= high) {
      int mid = (low + high) / 2;
      if (key < a[mid]) {
        high = mid - 1;
      } else if (key > a[mid]) {
        low = mid + 1;
      } else {
        return mid;
      }
    }
    return -1;
  }
}
