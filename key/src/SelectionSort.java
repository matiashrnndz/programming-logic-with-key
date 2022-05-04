package key;

public class SelectionSort {

  /*@ public normal_behavior
    @ requires arr != null && arr.length >= 1;
    @ ensures (\forall  int a, b;
    @                   0 <= a && a <= b && b < arr.length;
    @                   arr[a] <= arr[b]);
    @ ensures \dl_seqPerm((\seq_def int k; 0; arr.length; arr[k]), (\seq_def int k; 0; arr.length; \old(arr[k])));
    @*/
  public void selectionSort(int[] arr) {
    int i = 0;
    /*@ loop_invariant 0 <= i && i < arr.length;
      @ loop_invariant (\forall int a, b;
      @                         0 <= a && a < i && i <= b && b < arr.length;
      @                         arr[a] <= arr[b]);
      @ loop_invariant (\forall int a, b;
      @                         0 <= a && a <= b && b <= i;
      @                         arr[a] <= arr[b]);
      @ loop_invariant \dl_seqPerm((\seq_def int k; 0; arr.length; arr[k]), \old((\seq_def int k; 0; arr.length; arr[k])));
      @ assignable arr[*];
      @ decreases arr.length-1-i;
      @*/
    while(i != arr.length-1) {
      int j = i + 1;
      int min_idx = i;
      /*@ loop_invariant i < j && j <= arr.length;
        @ loop_invariant i <= min_idx && min_idx < arr.length;
        @ loop_invariant (\forall int k;
        @                         i <= k && k < j;
        @                         arr[min_idx] <= arr[k]);
        @ loop_invariant \dl_seqPerm((\seq_def int k; 0; arr.length; arr[k]), \old((\seq_def int k; 0; arr.length; arr[k])));
        @ assignable \strictly_nothing;
        @ decreases arr.length-j;
        @*/
      while(j != arr.length) {
        if (arr[j] < arr[min_idx]) {
          min_idx = j;
        }
        j++;
      }
      int temp = arr[min_idx];
      arr[min_idx] = arr[i];
      arr[i] = temp;
      i++;
    }
  }
}
