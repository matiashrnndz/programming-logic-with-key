package com.key;

public class QuickSortPartition {

  public static int[] arr;
  
  /*@ public normal_behavior
    @ requires arr != null
    @       && 0 <= l && l <= r && r < arr.length;
    @ ensures l <= \result && \result <= r 
    @      && (\forall int k;
    @                  l <= k && k < \result;
    @                  arr[k] < arr[\result])
    @      && (\forall int k;
    @                  \result < k && k <= r;
    @                  arr[k] >= arr[\result]);
    @ assignable arr[l..r];
    @*/
  public static int partition(int l, int r) {
    
    int i = l;
    int j = r;
    int pivot = arr[i];

    /*@ loop_invariant l <= i && i <= j && j <= r;
      @ loop_invariant (\forall int k;
      @                         l <= k && k < i;
      @                         arr[k] < arr[i]);
      @ loop_invariant (\forall int k;
      @                         j < k && k <= r;
      @                         arr[k] >= arr[i]);
      @ loop_invariant pivot == arr[i];
      @ assignable arr[l..r];
      @ decreases j - i;
      @*/
    while (i != j) {
      if (arr[i] <= arr[j]) {
        j--;
      } else {
        arr[i] = arr[j];
        arr[j] = arr[i+1];
        arr[i+1] = pivot;
        i++;
      }
    }
    return i;
  }
}
