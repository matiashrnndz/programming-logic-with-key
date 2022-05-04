package key;

public class SumArrayRecursive {

  /*@ public normal_behavior
    @ requires arr != null;
    @ ensures \result == (\sum int k;
    @                          0 <= k && k < arr.length;
    @                          arr[k]);
    @ assignable \nothing;
    @*/
  public int sumArrayRecursive(int[] arr) {
    return sumArrayRecursiveAux(arr, 0);
  }

  /*@ public normal_behavior
    @ requires arr != null;
    @ ensures \result == (\sum int k;
    @                          0 <= k && k < arr.length;
    @                          arr[k]);
    @ measured_by arr.length - i;
    @ assignable \nothing;
    @*/
    public int sumArrayRecursiveAux(int[] arr, int i) {
      if (i == arr.length) {
        return 0;
      }
      return arr[i] + sumArrayRecursiveAux(arr, ++i);
    }
}
