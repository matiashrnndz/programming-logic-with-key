package com.key;

public class QuickSort {

  public int[] arr;
  /*@ model \seq seqarr;
    @ represents seqarr = \dl_array2seq(arr);
    @*/
  
  /*@ public normal_behavior
    @ requires arr != null
    @       && 0 <= from && from <= to && to < arr.length;
    @ ensures from <= \result && \result <= to 
    @      && (\forall int k;
    @                  from <= k && k <= \result;
    @                  arr[k] < pivot)
    @      && (\forall int k;
    @                  \result <= k && k <= to;
    @                  pivot <= arr[k])
    @      && \dl_seqPerm(seqarr, \old(seqarr));
    @ assignable arr[*];
    @*/
  public int partition(int from, int to, int pivot) {
    
    int i = from - 1;
    int j = from;

    /*@ loop_invariant from <= j && j <= to;
      @ loop_invariant (\forall int k;
      @                         from <= k && k <= j;
      @                         arr[k] <= arr[j]);
      @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
      @ assignable arr[*];
      @ decreases to - j;
      @*/
    while (j < to) {

      if (arr[j] < pivot) {
        i++;
        int temp = arr[i];
        arr[i] = arr[j];
        arr[j] = temp;
      }
      j++;
    }

    int temp = arr[i+1];
    arr[i+1] = arr[to];
    arr[to] = temp;

    return i + 1;
  }
}
