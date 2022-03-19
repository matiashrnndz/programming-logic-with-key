package com.key;

public class LinearSearch {
  
  /*@ public normal_behavior
    @ ensures (0 <= \result && \result < arr.length && arr[\result] == key) 
    @      || (\result == -1 && !(\exists int k;
    @                                    0 <= k && k < arr.length;
    @                                    arr[k] == key));
    @ assignable \strictly_nothing;
    @*/
  public int linearSearch (int[] arr, int key) {
    int i = 0;
    /*@ loop_invariant 0 <= i && i <= arr.length;
      @ loop_invariant (\forall int k;
      @                         0 <= k && k < i;
      @                         arr[k] != key);
      @ assignable \strictly_nothing;
      @ decreases arr.length - i;
      @*/
    while (i != arr.length && arr[i] != key) {
      i = i + 1;
    }

    return i == arr.length ? -1 : i;
  }
}
