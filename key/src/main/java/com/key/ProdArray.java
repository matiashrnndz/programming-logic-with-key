package com.key;

public class ProdArray {

  /*@ public normal_behavior
    @ requires arr != null;
    @ ensures \result == (\product int k;
    @                              0 <= k && k < arr.length;
    @                              arr[k]);
    @ assignable \nothing;
    @*/
  private int prodArray(int[] arr) {
    int res = 1;
    /*@ loop_invariant 0 <= i && i <= arr.length;
      @ loop_invariant res == (\product int k;
      @                                 0 <= k && k < i;
      @                                 arr[k]);
      @ assignable \nothing;
      @ decreases arr.length-i;
      @*/
    for(int i=0; i < arr.length; i++) {
      res = res * arr[i];
    }
    return res;
  }
}
