package com.key;

public class IsUnique {

  public char[] s;

  /*@ model int n;
    @ represents n = s.length;
    @*/

  /*@ public normal_behavior
    @ requires s != null && s.length > 1;
    @ ensures (\result != (\exists int a, b;
    @                              0 <= a && a < b && b < s.length;
    @                              s[a] == s[b]));
    @*/
  public /*@ strictly_pure @*/ boolean is_unique() {
    /*@ loop_invariant 0 <= i && i < n;
      @ loop_invariant (\forall int a, b;
      @                         i <= a && a < b && b < n;
      @                         s[a] != s[b]);
      @ loop_invariant (\forall int a, b;
      @                         0 <= a && a <= i && i < b && b < n;
      @                         s[a] != s[b]);
      @ decreases i;
      @*/
    for(int i=s.length-1; 0<i; i--) {
      /*@ loop_invariant 0 <= j && j <= i;
        @ loop_invariant (\forall int a, b;
        @                         i <= a && a < b && b < n;
        @                         s[a] != s[b]);
        @ loop_invariant (\forall int a, b;
        @                         0 <= a && a <= i && i < b && b < n;
        @                         s[a] != s[b]);
        @ loop_invariant (\forall int k;
        @                         0 <= k < j;
        @                         s[k] != s[i]);
        @ decreases i-j;
        @*/
      for(int j=0; j<i; j++) {
        if(s[j] == s[i]) {
        /*@ ensures (\exists int a, b;
          @                  0 <= a && a < b && b < s.length;
          @                  s[a] == s[b]);
          @ signals_only \nothing;
          @*/
          return false;
        }
      }
    }
    return true;
  }
}
