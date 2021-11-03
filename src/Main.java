public class Main {
  
  public static void main(String[] args) {
    callLinearSearch();
  }

  private static void callLinearSearch() {
    int[] elems = {1, 2, 7, 3, 9, 12, 54, 87, 47, 15};
    int key = 54;
    int index = LinearSearch.linearSearch(elems, key);
    System.out.println(key + " was found at position: " + index);
  }

}
