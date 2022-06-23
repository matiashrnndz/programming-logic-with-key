package key;

public class QuickSortNuevo {

  /*@ public normal_behaviour
    @  ensures \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
    @  ensures (\forall int i; 0 <= i && i < arr.length-1; arr[i] <= arr[i+1]);
    @  assignable arr[*];
    @*/
    public void quicksort(int[] arr) {
      if(arr.length > 0) {
        sort(arr, 0, arr.length-1);
      }
    }

  /*@ public normal_behavior
    @  requires arr != null 
    @        && arr.length > 0
    @        && 0 <= l && l <= arr.length
    @        && -1 <= r && r < arr.length
    @        && l <= r + 1;
    @  requires l >= 0 ==> (\forall int i; 0 <= i && i < l; arr[i] <= arr[l]);
    @  requires r < arr.length ==> (\forall int i; r < i && i < arr.length; arr[r] <= arr[i]);
    @  ensures (\forall int i; l <= i && i < r; arr[i] <= arr[i+1]);
    @  ensures l >= 0 ==> (\forall int i; 0 <= i && i < l; arr[i] <= arr[l]);
    @  ensures r < arr.length ==> (\forall int i; r < i && i < arr.length; arr[r] <= arr[i]);
    @  ensures \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
    @  measured_by r - l + 1;
    @  assignable arr[l..r];
    @*/
  private static void sort(int[] arr, int l, int r) {
    if (l < r) {
      int p = partition(arr, l, r);
      sort(arr, l, p-1);
      sort(arr, p+1, r);
    }
  }

  /*@ public normal_behavior
    @  requires arr != null
    @        && 0 <= l && l <= r && r < arr.length;
    @  ensures l <= \result && \result <= r
    @       && (\forall int k; l <= k && k < \result; arr[k] < arr[\result])
    @       && (\forall int k; \result < k && k <= r; arr[k] >= arr[\result]);
    @  ensures \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
    @  assignable arr[l..r];
    @*/
  private static int partition(int[] arr, int l, int r) {

    int i = l;
    int j = r;
    int pivot = arr[i];

    /*@  loop_invariant pivot == arr[i];
      @  loop_invariant l <= i && i <= j && j <= r;
      @  loop_invariant (\forall int k; l <= k && k < i; arr[k] < arr[i]);
      @  loop_invariant (\forall int k; j < k && k <= r; arr[k] >= arr[i]);
      @  loop_invariant \dl_seqPerm(\dl_array2seq(arr), \old(\dl_array2seq(arr)));
      @  assignable arr[l..r];
      @  decreases j - i;
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
