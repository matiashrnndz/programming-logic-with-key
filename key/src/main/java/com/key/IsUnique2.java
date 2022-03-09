package com.key;

public class IsUnique2 {

  public char[] s;
  /*@ model int n;
    @ represents n = s.length;
    @*/

  /*@ public normal_behavior
    @ ensures (\result <==> (\forall int a, b;
    @                               0 <= a && a < s.length && 0 <= b && b < s.length;
    @                               a != b ==> s[a] != s[b]));
    @*/
  public boolean is_unique2() {
    boolean b = true;
    int i = 0;
    /*@ loop_invariant 0 <= i && i <= n;
      @ loop_invariant (b <==> (\forall int a, b;
      @                                0 <= a && a < i && 0 <= b && b < i;
      @                                a != b ==> s[a] != s[b]));
      @ assignable \nothing;
      @ decreases n - i;
      @*/
    while (b && i != s.length) {
      int j = 0;
      /*@ loop_invariant 0 <= j && j <= i;
        @ loop_invariant (\forall int k;
        @                         0 <= k < j;
        @                         s[k] != s[i]);
        @ assignable \nothing;
        @ decreases i - j;
        @*/
      while (j != i && s[j] != s[i]) {
        j = j+1;
      }
      b = j == i;
      i = i+1;
    }
    return b;
  }
}
