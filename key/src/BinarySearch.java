package key;

public class BinarySearch {
  
  /*@ public normal_behavior
    @ requires (\forall int a, b;
    @                   0 <= a && a <= b && b < arr.length;
    @                   arr[a] <= arr[b]);
    @ ensures (\result == -1 ==>
    @           (\forall int k;
    @                    0 <= k && k < arr.length;
    @                    arr[k] != key));
    @ ensures (result >= 0 ==>
    @           result < arr.length && arr[\result] == key); 
    @*/
  public int binarySearch(int[] arr, int key){
    int l = 0;
    int r = arr.length;
    int m = (l+r)/2;
    /*@ loop_invariant 0 <= l && l <= r && r <= arr.length;
      @ loop_invariant m == (l+r)/2;
      @ loop_invariant (\forall int k;
      @                         0 <= k < l;
      @                         arr[k] != key);
      @ loop_invariant (\forall int k;
      @                         r <= k < arr.length;
      @                         arr[k] != key);
      @ assignable \strictly_nothing;
      @ decreasing r - l;
      @*/
    while (l != r && key != arr[m]) {
      if (key < arr[m]) r = m;
      else l = m + 1;
      m = (l+r)/2;
    }
    return (l == r ? -1 : m);
  }
}
