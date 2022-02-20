package com.key;

public class SumArray {

  /*@ public normal_behavior
    @ requires arr != null && arr.length > 0;
    @ ensures \result == (\sum int k;
    @                          0 <= k && k < arr.length;
    @                          arr[k]);
    @ assignable \nothing;
    @*/
    private int sumArray(int[] arr) {
      int res = 0;
      /*@ loop_invariant 0 <= i && i <= arr.length;
        @ loop_invariant res == (\sum int k;
        @                             0 <= k && k < i;
        @                             arr[k]);
        @ assignable \nothing;
        @ decreases arr.length-i;
        @*/
      for(int i=0; i < arr.length; i++) {
        res = res + arr[i];
      }
      return res;
    }
}
