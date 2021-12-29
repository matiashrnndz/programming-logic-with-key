package com.key;

public class BubbleSort {

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
  public void bubbleSort() {
    /*@ loop_invariant 0 <= i && i < n;
      @ loop_invariant (\forall int a, b; n-1-i <= a && a <= b && b < n; arr[a] <= arr[b]);
      @ loop_invariant (\forall int a, b; 0 <= a && a <= n-1-i && n-1-i < b && b < n; arr[a] <= arr[b]);
      @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
      @ assignable arr[*];
      @ decreases n-1-i;
      @*/
    for(int i=0; i < arr.length-1; i++) {
      /*@ loop_invariant 0 <= j && j <= n-1-i;
        @ loop_invariant (\forall int a, b; n-1-i <= a && a <= b && b < n; arr[a] <= arr[b]);
        @ loop_invariant (\forall int a, b; 0 <= a && a <= n-1-i && n-1-i < b && b < n; arr[a] <= arr[b]);
        @ loop_invariant (\forall int k; 0 <= k && k <= j; arr[k] <= arr[j]);
        @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
        @ assignable arr[*];
        @ decreases n-1-i-j;
        @*/
      for(int j=0; j < arr.length-1-i; j++) {
        if (arr[j] > arr[j+1]) {
          int old = arr[j+1];
          arr[j+1] = arr[j];
          arr[j] = old;
        }
      }
    }
  }
}

/* example n=5

i=0  : 9 8 7 6 5                (n-1-i = 5-1-0 = 4)
  j=0: 9 8 7 6 5 -> 8 9 7 6 5
  j=1: 8 9 7 6 5 -> 8 7 9 6 5
  j=2: 8 7 9 6 5 -> 8 7 6 9 5
  j=3: 8 7 6 9 5 -> 8 7 6 5 9

i=1  : 8 7 6 5 9                (n-1-i = 5-1-1 = 3)
  j=0: 8 7 6 5 9 -> 7 8 6 5 9
  j=1: 7 8 6 5 9 -> 7 6 8 5 9
  j=2: 7 6 8 5 9 -> 7 6 5 8 9

i=2  : 7 6 5 8 9                (n-1-i = 5-1-2 = 2)
  j=0: 7 6 5 8 9 -> 6 7 5 8 9
  j=1: 6 7 5 8 9 -> 6 5 7 8 9

i=3  : 6 5 7 8 9                (n-1-i = 5-1-3 = 1)
  j=0: 6 5 7 8 9 -> 5 6 7 8 9
*/
