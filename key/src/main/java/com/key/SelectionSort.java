package com.key;

public class SelectionSort {

  public /*@ non_null @*/ int[] arr;
  /*@ model \seq seqarr;
    @ represents seqarr = \dl_array2seq(arr);
    @*/

  /*@ public normal_behavior
    @ requires arr != null && arr.length >= 1;
    @ ensures (\forall int a, b; 0 <= a && a <= b && b < arr.length; arr[a] <= arr[b]);
    @ ensures \dl_seqPerm(seqarr, \old(seqarr));
    @*/
  public void selectionSort() {
    /*@ loop_invariant 0 <= i && i < arr.length;
      @ loop_invariant (\forall int a, b; 0 <= a && a < i && a <= b && b < arr.length; arr[a] <= arr[b]);
      @ loop_invariant (\forall int a, b; 0 <= a && a <= b && b <= i; arr[a] <= arr[b]);
      @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
      @ assignable arr[*];
      @ decreases arr.length-1-i;
      @*/
    for (int i = 0; i < arr.length-1; i++) {
      int min_idx = i;
      /*@ loop_invariant 0 <= i && i < j && j <= arr.length;
        @ loop_invariant i <= min_idx && min_idx < arr.length;
        @ loop_invariant (\forall int k; 0 <= k && k < i; arr[min_idx] >= arr[k]);
        @ loop_invariant (\forall int k; i <= k && k < j; arr[min_idx] <= arr[k]);
        @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
        @ assignable \strictly_nothing;
        @ decreases arr.length-j;
        @*/
      for (int j = i+1; j < arr.length; j++) {
        if (arr[j] < arr[min_idx]) {
          min_idx = j;
        }
      }
      int old = arr[min_idx];
      arr[min_idx] = arr[i];
      arr[i] = old;
    }
  }
}
