package key;

public class ProdArrayRecursive {

  /*@ public normal_behavior
    @ requires arr != null;
    @ ensures \result == (\product int k;
    @                              0 <= k && k < arr.length;
    @                              arr[k]);
    @ assignable \nothing;
    @*/
    public int prodArrayRecursive(int[] arr) {
      return prodArrayRecursiveAux(arr, 0);
    }

  /*@ public normal_behavior
    @ requires arr != null;
    @ ensures \result == (\product int k;
    @                              0 <= k && k < arr.length;
    @                              arr[k]);
    @ assignable \nothing;
    @*/
  public int prodArrayRecursiveAux(int[] arr, int i) {
    if (i == arr.length) {
      return 1;
    }
    return arr[i] * prodArrayRecursiveAux(arr, ++i);
  }
}
