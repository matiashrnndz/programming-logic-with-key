package com.key;

public class LinearSearch {
  
  /*@ public normal_behavior
    @ ensures \result >= 0 ==>
    @           \result < arr.length && arr[\result] == key;
    @ ensures \result < 0 ==>
    @           (\forall  int k;
    @                     0 <= k && k < arr.length;
    @                     arr[k] != key);
    @ assignable \strictly_nothing;
    @*/
  public int linearSearch (int[] arr, int key) {
    /*@ loop_invariant 0 <= i && i <= arr.length;
      @ loop_invariant (\forall int k;
      @                         0 <= k && k < i;
      @                         arr[k] != key);
      @ assignable \strictly_nothing;
      @ decreases arr.length - i;
      @*/
    for (int i = 0; i < arr.length; i++) {
      if (arr[i] == key) return i;
    }
    return -1;
  }
}
