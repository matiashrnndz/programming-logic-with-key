package key;

public class QuickSort2 {

  /*@ public normal_behavior
    @ requires arr != null
    @       && 0 <= l && l <= arr.length
    @       && -1 <= r && r < arr.length
    @       && l <= r + 1;
    @ ensures (\forall int a, b;
    @                  0 <= l && l <= a && a <= b && b <= r && r < arr.length;
    @                  arr[a] <= arr[b]);
    @ ensures (\forall int k;
    @                  l <= k && k <= r;
    @                  (\exists int m;
    @                           l <= m && m <= r;
    @                           arr[k] == \old(arr)[m]));
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
    @      && (\forall int k;
    @                  l <= k && k < \result;
    @                  arr[k] < arr[\result])
    @      && (\forall int k;
    @                  \result < k && k <= r;
    @                  arr[k] >= arr[\result]);
    @ ensures (\forall int k;
    @                  l <= k && k <= r;
    @                  (\exists int m;
    @                           l <= m && m <= r;
    @                           arr[k] == \old(arr)[m]));
    @*/
  public static int partition(int[] arr, int l, int r) {

    int i = l;
    int j = r;
    int pivot = arr[i];

    /*@ loop_invariant pivot == arr[i];
      @ loop_invariant l <= i && i <= j && j <= r;
      @ loop_invariant (\forall int k;
      @                         l <= k && k < i;
      @                         arr[k] < arr[i]);
      @ loop_invariant (\forall int k;
      @                         j < k && k <= r;
      @                         arr[k] >= arr[i]);
      @ loop_invariant (\forall int k;
      @                         l <= k && k <= r;
      @                         (\exists int m;
      @                                  l <= m && m <= r;
      @                                  arr[k] == \old(arr)[m]));
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
