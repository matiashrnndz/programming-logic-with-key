package key;

public class InsertionSort {

  /*@ public normal_behavior
    @ requires arr != null && arr.length > 0;
    @ ensures (\forall int a, b;
    @                  0 <= a && a <= b && b < arr.length;
    @                  arr[a] <= arr[b]);
    @ ensures \dl_seqPerm((\seq_def int k; 0; arr.length; arr[k]), \old((\seq_def int k; 0; arr.length; arr[k])));
    @ assignable arr[*];
    @*/
  public void insertionSort(int[] arr) {
    int i = 1;
    /*@ loop_invariant 1 <= i && i <= arr.length;
      @ loop_invariant (\forall int a, b;
      @                         0 <= a && a <= b && b < arr.length && b < i;
      @                         arr[a] <= arr[b]);
      @ loop_invariant \dl_seqPerm((\seq_def int k; 0; arr.length; arr[k]), \old((\seq_def int k; 0; arr.length; arr[k])));
      @ assignable arr[*];
      @ decreases arr.length - i;
      @*/
    while (i != arr.length) {
      int j = i;
      /*@ loop_invariant 0 <= j && j <= i;
        @ loop_invariant (\forall int a, b;
        @                         0 <= a && a < b && b <= i && b != j;
        @                         arr[a] <= arr[b]);
        @ loop_invariant \dl_seqPerm((\seq_def int k; 0; arr.length; arr[k]), \old((\seq_def int k; 0; arr.length; arr[k])));
        @ assignable arr[*];
        @ decreases j;
        @*/
      while (j != 0 && arr[j-1] > arr[j]) {
        int temp = arr[j];
        arr[j] = arr[j-1];
        arr[j-1] = temp;
        j--;
      }
      i++;
    }
  }
}
