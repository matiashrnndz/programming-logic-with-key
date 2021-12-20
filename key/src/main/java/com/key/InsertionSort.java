package com.key;

public class InsertionSort {

  public int[] a;
  /*@ model \seq seqa;
    @ represents seqa = \dl_array2seq(a);
    @*/

  /*@ public normal_behavior
    @ requires a != null && a.length > 0;
    @ ensures (\forall int m, n; 0 <= m && m <= n && n < a.length; a[m] <= a[n]);
    @ ensures \dl_seqPerm(seqa, \old(seqa));
    @ assignable a[*];
    @*/
  public void insertionSort() {
    /*@ loop_invariant 1 <= i && i <= a.length;
      @ loop_invariant (\forall int m, n; 0 <= m && m <= n && n < a.length && n <= i-1; a[m] <= a[n]);
      @ loop_invariant \dl_seqPerm(seqa, \old(seqa));
      @ assignable a[*];
      @ decreases a.length - i;
      @*/
    for (int i = 1; i < a.length; i++) {
      /*@ loop_invariant 1 <= i && i <= a.length-1;
        @ loop_invariant 0 <= j && j <= i;
        @ loop_invariant (\forall int m, n; 0 <= m && m < n && n < i+1 && n != j; a[m] <= a[n]);
        @ loop_invariant \dl_seqPerm(seqa, \old(seqa));
        @ assignable a[*];
        @ decreases j;
        @*/
      for (int j = i; j > 0 && a[j-1] > a[j]; j--) {
        int oldaj = a[j];
        a[j] = a[j-1];
        a[j-1] = oldaj;
      }
    }
  }
}
