package key;

public class SumArray {

  /*@ public normal_behavior
    @ requires arr != null;
    @ ensures \result == (\sum int k;
    @                          0 <= k && k < arr.length;
    @                          arr[k]);
    @ assignable \nothing;
    @*/
    public int sumArray(int[] arr) {
      int res = 0;
      int i = 0;
      /*@ loop_invariant 0 <= i && i <= arr.length;
        @ loop_invariant res == (\sum int k;
        @                             0 <= k && k < i;
        @                             arr[k]);
        @ assignable \nothing;
        @ decreases arr.length-i;
        @*/
      while (i != arr.length) {
        res = res + arr[i];
        i++;
      }
      return res;
    }
}
