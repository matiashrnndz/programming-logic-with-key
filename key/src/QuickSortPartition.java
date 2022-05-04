package key;

public class QuickSortPartition {

  /*@ public normal_behavior
    @ requires arr != null
    @       && 0 <= l && l <= r && r < arr.length;
    @ ensures l <= \result && \result <= r 
    @      && (\forall int k;
    @                  l <= k && k < \result;
    @                  arr[k] < arr[\result])
    @      && (\forall int k;
    @                  \result < k && k <= r;
    @                  arr[k] >= arr[\result]);
    @ ensures \dl_seqPerm((\seq_def int k; l; r+1; arr[k]), (\seq_def int k; l; r+1; \old(arr[k])));
    @ ensures (\seq_def int k; 0; l; arr[k]) == (\seq_def int k; 0; l; \old(arr[k]));
    @ ensures (\seq_def int k; r+1; arr.length; arr[k]) == (\seq_def int k; r+1; arr.length; \old(arr[k]));
    @*/
  public static int partition(int[] arr, int l, int r) {

    int i = l;
    int j = r;
    int pivot = arr[i];

    /*@ loop_invariant l <= i && i <= j && j <= r;
      @ loop_invariant (\forall int k;
      @                         l <= k && k < i;
      @                         arr[k] < arr[i]);
      @ loop_invariant (\forall int k;
      @                         j < k && k <= r;
      @                         arr[k] >= arr[i]);
      @ loop_invariant pivot == arr[i];
      @ loop_invariant \dl_seqPerm((\seq_def int k; l; r+1; arr[k]), (\seq_def int k; l; r+1; \old(arr[k])));
      @ loop_invariant (\seq_def int k; 0; l; arr[k]) == (\seq_def int k; 0; l; \old(arr[k]));
      @ loop_invariant (\seq_def int k; r+1; arr.length; arr[k]) == (\seq_def int k; r+1; arr.length; \old(arr[k]));
      @ assignable arr[l..r];
      @ decreases j - i;
      @*/
    while (i != j) {
      if (arr[i] <= arr[j]) {
        j--;
      } else {
        arr[i] = arr[j];
        arr[j] = arr[i+1];
        arr[i+1] = pivot;
        i++;
      }
    }
    return i;
  }
}
