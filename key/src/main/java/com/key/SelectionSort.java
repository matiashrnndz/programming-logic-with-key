package com.key;

public class SelectionSort {

  public int[] arr;
  /*@ model \seq seqarr;
    @ represents seqarr = \dl_array2seq(arr);
    @*/

  /*@ model int N;
    @ represents N = arr.length;
    @*/

  /*@ public normal_behavior
    @ requires arr != null && arr.length >= 1;
    @ ensures (\forall  int a, b;
    @                   0 <= a && a <= b && b < arr.length;
    @                   arr[a] <= arr[b]);
    @ ensures \dl_seqPerm(seqarr, \old(seqarr));
    @*/
  public void selectionSort() {
    int i = 0;
    /*@ loop_invariant 0 <= i && i < N;
      @ loop_invariant (\forall int a, b;
      @                         0 <= a && a < i && i <= b && b < N;
      @                         arr[a] <= arr[b]);
      @ loop_invariant (\forall int a, b;
      @                         0 <= a && a <= b && b <= i;
      @                         arr[a] <= arr[b]);
      @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
      @ assignable arr[*];
      @ decreases N-1-i;
      @*/
    while(i != arr.length-1) {
      int j = i + 1;
      int min_idx = i;
      /*@ loop_invariant i < j && j <= N;
        @ loop_invariant i <= min_idx && min_idx < N;
        @ loop_invariant (\forall int k;
        @                         i <= k && k < j;
        @                         arr[min_idx] <= arr[k]);
        @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
        @ assignable \strictly_nothing;
        @ decreases N-j;
        @*/
      while(j != arr.length) {
        if (arr[j] < arr[min_idx]) {
          min_idx = j;
        }
        j++;
      }
      int temp = arr[min_idx];
      arr[min_idx] = arr[i];
      arr[i] = temp;
      i++;
    }
  }
}
