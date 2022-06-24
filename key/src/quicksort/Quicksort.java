public class Quicksort {

  /*@ public normal_behaviour
    @  ensures (\forall int a, b; 0 <= a && a <= b && b < array.length; array[a] <= array[b]);
    @  ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
    @  assignable array[*];
    @*/
    public void quicksort(int[] array) {
      if(array.length > 0) {
          sort(array, 0, array.length-1);
      }
  }

  /*@ public normal_behavior
    @ requires array != null;
    @ requires 0 <= l && l <= array.length;
    @ requires -1 <= r && r < array.length;
    @ requires l <= r + 1;
    @ requires l > 0 ==> (\forall int i; l <= i && i <= r; array[l-1] <= array[i]);
    @ requires r < array.length-1 ==> (\forall int i; l <= i && i <= r; array[i] <= array[r+1]);
    @ ensures (\forall int a, b; l <= a && a <= b && b <= r; array[a] <= array[b]);
    @ ensures l > 0 ==> (\forall int i; l <= i && i <= r; array[l-1] <= array[i]);
    @ ensures r < array.length-1 ==> (\forall int i; l <= i && i <= r; array[i] <= array[r+1]);
    @ ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
    @ measured_by r - l + 1;
    @ assignable array[l..r];
    @*/
  private static void sort(int[] array, int l, int r) {
    if (l < r) {
      int p = split(array, l, r);
      sort(array, l, p-1);
      sort(array, p+1, r);
    }
  }

  /*@ public normal_behavior
    @ requires array != null
    @ requires 0 <= l && l <= r && r < array.length;
    @ requires l > 0 ==> (\forall int i; l <= i && i <= r; array[l-1] <= array[i]);
    @ requires r < array.length-1 ==> (\forall int i; l <= i && i <= r; array[i] <= array[r+1]);
    @ ensures l <= \result && \result <= r
    @ ensures (\forall int k; l <= k && k < \result; array[k] < array[\result])
    @ ensures (\forall int k; \result < k && k <= r; array[k] >= array[\result]);
    @ ensures l > 0 ==> (\forall int i; l <= i && i <= r;  array[l-1] <= array[i]);
    @ ensures r < array.length-1 ==> (\forall int i; l <= i && i <= r; array[i] <= array[r+1]);
    @ ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
    @ assignable array[l..r];
    @*/
  private static int split(int[] array, int l, int r) {

    int i = l;
    int j = r;
    int pivot = array[i];

    /*@ loop_invariant pivot == array[i];
      @ loop_invariant l <= i && i <= j && j <= r;
      @ loop_invariant (\forall int k; l <= k && k < i; array[k] < array[i]);
      @ loop_invariant (\forall int k; j < k && k <= r; array[k] >= array[i]);
      @ loop_invariant l > 0 ==> (\forall int i; l <= i && i <= r; array[l-1] <= array[i]);
      @ loop_invariant r < array.length-1 ==> (\forall int i; l <= i && i <= r; array[i] <= array[r+1]);
      @ loop_invariant \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
      @ assignable array[l..r];
      @ decreases j - i;
      @*/
    while (i != j) {
      if (array[i] <= array[j]) {
        j--;
      } else {
        array[i] = array[j];
        array[j] = array[i+1];
        array[i+1] = pivot;
        i++;
      }
    }
    return i;
  }
}
