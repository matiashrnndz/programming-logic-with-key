package com.key;

public class GreatestCommonDivisor {
  /*@ public normal_behavior
    @ requires _small >= 0 && _big >= _small;
    @ ensures _big != 0 ==>
    @           (_big % \result == 0 &&
    @           _small % \result == 0 &&
    @           (\forall int x;
    @                    x > 0 && _big % x == 0 && _small % x == 0;
    @                    \result % x == 0));
    @ assignable \nothing;
    @*/
    private int gcd(int _big, int _small) {
      int big = _big;
      int small = _small;
  
      /*@ loop_invariant small >= 0 && big >= small;
        @ loop_invariant big == 0 ==> _big == 0;
        @ loop_invariant (\forall int x;
        @                         x > 0;
        @                         (_big % x == 0 && _small % x == 0) <==>
        @                           (big % x == 0 && small % x == 0));
        @ decreases small;
        @ assignable \nothing;
        @*/
      while (small != 0) {
        final int t = big % small;
        big = small;
        small = t;
      }
      
      return big;
    }
}
