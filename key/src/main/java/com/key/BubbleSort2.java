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
    @ ensures (\forall  int a, b;
    @                   0 <= a && a <= b && b < arr.length;
    @                   arr[a] <= arr[b]);
    @ ensures \dl_seqPerm(seqarr, \old(seqarr));
    @*/
  public void bubbleSort2() {
    /*@ loop_invariant 0 <= i && i < n;
      @ loop_invariant (\forall int a, b;
      @                         i <= a && a <= b && b < n;
      @                         arr[a] <= arr[b]);
      @ loop_invariant (\forall int a, b;
      @                         0 <= a && a <= i && i < b && b < n;
      @                         arr[a] <= arr[b]);
      @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
      @ assignable arr[*];
      @ decreases i;
      @*/
    for(int i=arr.length-1; 0 < i; i--) {
      /*@ loop_invariant 0 <= j && j <= i;
        @ loop_invariant (\forall int a, b;
        @                         i <= a && a <= b && b < n;
        @                         arr[a] <= arr[b]);
        @ loop_invariant (\forall int a, b;
        @                         0 <= a && a <= i && i < b && b < n;
        @                         arr[a] <= arr[b]);
        @ loop_invariant (\forall int k;
                                  0 <= k && k <= j;
                                  arr[k] <= arr[j]);
        @ loop_invariant \dl_seqPerm(seqarr, \old(seqarr));
        @ assignable arr[*];
        @ decreases i-j;
        @*/
      for(int j=0; j < i; j++) {
        if (arr[j] > arr[j+1]) {
          int temp = arr[j+1];
          arr[j+1] = arr[j];
          arr[j] = temp;
        }
      }
    }
  }
}

/* example n=5

i=4 : [9, 8, 7, 6, 5]

-  j=0 : [9, 8, 7, 6, 5] -> [8, 9, 7, 6, 5]
-  j=1 : [8, 9, 7, 6, 5] -> [8, 7, 9, 6, 5]
-  j=2 : [8, 7, 9, 6, 5] -> [8, 7, 6, 9, 5]
-  j=3 : [8, 7, 6, 9, 5] -> [8, 7, 6, 5, 9]

i=3 : [8, 7, 6, 5, 9]

-  j=0 : [8, 7, 6, 5, 9] -> [7, 8, 6, 5, 9]
-  j=1 : [7, 8, 6, 5, 9] -> [7, 6, 8, 5, 9]
-  j=2 : [7, 6, 8, 5, 9] -> [7, 6, 5, 8, 9]

i=2 : [7, 6, 5, 8, 9]

-  j=0 : [7, 6, 5, 8, 9] -> [6, 7, 5, 8, 9]
-  j=1 : [6, 7, 5, 8, 9] -> [6, 5, 7, 8, 9]

i=1 : [6, 5, 7, 8, 9]

-  j=0 : [6, 5, 7, 8, 9] -> [5, 6, 7, 8, 9]

*/