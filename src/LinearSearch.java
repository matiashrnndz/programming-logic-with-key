public class LinearSearch {
  /*@ public normal_behavior
    @ ensures 0 <= \result ==> \result < a.length && a[\result] == key;
    @ ensures \result < 0 ==> (\forall int x; 0 <= x && x < a.length; a[x] != key);
    @ assignable \strictly_nothing;
    @*/
  public static int linearSearch (int[] a, int key) {
    int i = 0;
    /*@ loop_invariant 0 <= i && i <= a.length;
      @ loop_invariant (\forall int k; 0 <= k && k < i; a[k] != key);
      @ assignable \strictly_nothing;
      @ decreases a.length - i;
      @*/
    while (i < a.length) {
      if (a[i] == key) {
        return i;
      }
      i = i + 1;
    }
    return -1;
  }
}
