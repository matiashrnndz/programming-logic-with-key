package com.key;

public class BinarySearchOpt2 {
  
  /*@ public normal_behavior
    @ requires (\forall int i, j; 0 <= i && i <= j && j < a.length; a[i] <= a[j]);
    @ ensures (\result == -1 ==> (\forall int i; 0 <= i && i < a.length; a[i] != x));
    @ ensures (0 <= result ==> result < a.length && a[\result] == x); 
    @*/
  public int binarySearch(int x, int[] a){
    int l = 0, r = a.length, m = (l+r)/2;
    /*@ loop_invariant 0 <= l && l <= r && r <= a.length;
      @ loop_invariant m == (l+r)/2;
      @ loop_invariant (\forall int i; 0 <= i < l; a[i] != x);
      @ loop_invariant (\forall int i ; r <= i < a.length ; a[i] != x);
      @ assignable \strictly_nothing;
      @ decreasing r - l;
      @*/
    while (l != r && x != a[m]) {
      if (x < a[m]) r = m;
      else l = m + 1;
      m = (l+r)/2;
    }
    return (l == r ? -1 : m);
  }
}
