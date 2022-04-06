package com.key;

public class ProdArray {

  /*@ public normal_behavior
    @ requires arr != null;
    @ ensures \result == (\product int k;
    @                              0 <= k && k < arr.length;
    @                              arr[k]);
    @ assignable \nothing;
    @*/
  public int prodArray(int[] arr) {
    int res = 1;
    int i = 0;
    /*@ loop_invariant 0 <= i && i <= arr.length;
      @ loop_invariant res == (\product int k;
      @                                 0 <= k && k < i;
      @                                 arr[k]);
      @ assignable \nothing;
      @ decreases arr.length-i;
      @*/
    while (i != arr.length) {
      res = res * arr[i];
      i++;
    }
    return res;
  }
}
