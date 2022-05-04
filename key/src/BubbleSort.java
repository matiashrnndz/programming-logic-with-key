package key;

public class BubbleSort {

  /*@ public normal_behavior
    @ requires arr != null && arr.length > 0;
    @ ensures (\forall  int a, b;
    @                   0 <= a && a <= b && b < arr.length;
    @                   arr[a] <= arr[b]);
    @ ensures \dl_seqPerm((\seq_def int k; 0; arr.length; arr[k]), \old((\seq_def int k; 0; arr.length; arr[k])));
    @ assignable arr[*];
    @*/
  public void bubbleSort(int[] arr) {
    int i=arr.length-1;
    /*@ loop_invariant 0 <= i && i < arr.length;
      @ loop_invariant (\forall int a, b;
      @                         i <= a && a <= b && b < arr.length;
      @                         arr[a] <= arr[b]);
      @ loop_invariant (\forall int a, b;
      @                         0 <= a && a <= i && i < b && b < arr.length;
      @                         arr[a] <= arr[b]);
      @ loop_invariant \dl_seqPerm((\seq_def int k; 0; arr.length; arr[k]), \old((\seq_def int k; 0; arr.length; arr[k])));
      @ assignable arr[*];
      @ decreases i;
      @*/
    while(i != 0) {
      int j = 0;
      /*@ loop_invariant 0 <= j && j <= i;
        @ loop_invariant (\forall int a, b;
        @                         i <= a && a <= b && b < arr.length;
        @                         arr[a] <= arr[b]);
        @ loop_invariant (\forall int a, b;
        @                         0 <= a && a <= i && i < b && b < arr.length;
        @                         arr[a] <= arr[b]);
        @ loop_invariant (\forall int k;
        @                         0 <= k && k <= j;
        @                         arr[k] <= arr[j]);
        @ loop_invariant \dl_seqPerm((\seq_def int k; 0; arr.length; arr[k]), \old((\seq_def int k; 0; arr.length; arr[k])));
        @ assignable arr[*];
        @ decreases i-j;
        @*/
      while(j != i) {
        if (arr[j] > arr[j+1]) {
          int temp = arr[j+1];
          arr[j+1] = arr[j];
          arr[j] = temp;
        }
        j++;
      }
      i--;
    }
  }
}

/* example arr.length=5
i=4 : [9, 8, 7, 6, 5]
-  j=0 : [9, 8, 7, 6, 5] -> [8, 9, 7, 6, 5]
-  j=1 : [8, 9, 7, 6, 5] -> [8, 7, 9, 6, 5]
-  j=2 : [8, 7, 9, 6, 5] -> [8, 7, 6, 9, 5]
-  j=3 : [8, 7, 6, 9, 5] -> [8, 7, 6, 5, 9]
i=3 : [8, 7, 6, 5, 9]
-  j=0 : [8, 7, 6, 5, 9] -> [7, 8, 6, 5, 9]
-  j=1 : [7, 8, 6, 5, 9] -> [7, 6, 8, 5, 9]
-  j=2 : [7, 6, 8, 5, 9] -> [7, 6, 5, 8, 9]
i=2 : [7, 6, 5, 8, 9]
-  j=0 : [7, 6, 5, 8, 9] -> [6, 7, 5, 8, 9]
-  j=1 : [6, 7, 5, 8, 9] -> [6, 5, 7, 8, 9]
i=1 : [6, 5, 7, 8, 9]
-  j=0 : [6, 5, 7, 8, 9] -> [5, 6, 7, 8, 9]
*/
