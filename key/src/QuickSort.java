package key;

public class QuickSort {

  /*@ public normal_behavior
    @ requires arr != null 
    @       && arr.length > 0
    @       && 0 <= l && l <= arr.length
    @       && -1 <= r && r < arr.length
    @       && l <= r + 1;
    @ ensures (\forall int a, b; l <= a && a <= b && b <= r; arr[a] <= arr[b]);
    @ ensures (\dl_seqPerm((\seq_def int k; l; r+1; arr[k]), (\seq_def int k; l; r+1; \old(arr)[k])));
    @ measured_by r - l + 1;
    @ assignable arr[l..r];
    @*/
  public static void quicksort(int[] arr, int l, int r) {
    if (l < r) {
      int p = partition(arr, l, r);
      quicksort(arr, l, p-1);
      quicksort(arr, p+1, r);
    }
  }

  /*@ public normal_behavior
    @ requires arr != null
    @       && 0 <= l && l <= r && r < arr.length;
    @ ensures l <= \result && \result <= r
    @      && (\forall int k; l <= k && k < \result; arr[k] < arr[\result])
    @      && (\forall int k; \result < k && k <= r; arr[k] >= arr[\result]);
    @ ensures (\dl_seqPerm((\seq_def int k; l; r+1; arr[k]), (\seq_def int k; l; r+1; \old(arr)[k])));
    @ assignable arr[l..r];
    @*/
  public static int partition(int[] arr, int l, int r) {

    int i = l;
    int j = r;
    int pivot = arr[i];

    /*@ loop_invariant pivot == arr[i];
      @ loop_invariant l <= i && i <= j && j <= r;
      @ loop_invariant (\forall int k; l <= k && k < i; arr[k] < arr[i]);
      @ loop_invariant (\forall int k; j < k && k <= r; arr[k] >= arr[i]);
      @ loop_invariant (\dl_seqPerm((\seq_def int k; l; r+1; arr[k]), (\seq_def int k; l; r+1; \old(arr)[k])));
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
