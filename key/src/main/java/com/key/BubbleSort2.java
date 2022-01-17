package com.key;

public class BubbleSort2 {

  public int[] arr;
  /*@ model \seq seqarr;
    @ represents seqarr = \dl_array2seq(arr);
    @*/

  /*@ model int n;
    @ represents n = arr.length;
    @*/

  /*@ public normal_behavior
    @ requires arr != null && arr.length >= 1;
    @ ensures (\forall int a, b; 0 <= a && a <= b && b < arr.length; arr[a] <= arr[b]);
    @ ensures \dl_seqPerm(seqarr, \old(seqarr));
    @*/
  public void bubbleSort2() {
    /*@ loop_invariant 0 <= i && i < n;
      @ loop_invariant (\forall int a, b; i <= a && a <= b && b < n; arr[a] <= arr[b]);
      @ loop_invariant (\forall int a, b; 0 <= a && a <= i && i < b && b < n; arr[a] <= arr[b]);
      @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
      @ assignable arr[*];
      @ decreases i;
      @*/
    for(int i=arr.length-1; 0 < i; i--) {
      /*@ loop_invariant 0 <= j && j <= i;
        @ loop_invariant (\forall int a, b; i <= a && a <= b && b < n; arr[a] <= arr[b]);
        @ loop_invariant (\forall int a, b; 0 <= a && a <= i && i < b && b < n; arr[a] <= arr[b]);
        @ loop_invariant (\forall int k; 0 <= k && k <= j; arr[k] <= arr[j]);
        @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
        @ assignable arr[*];
        @ decreases i-j;
        @*/
      for(int j=0; j < i; j++) {
        if (arr[j] > arr[j+1]) {
          int old = arr[j+1];
          arr[j+1] = arr[j];
          arr[j] = old;
        }
      }
    }
  }
}
