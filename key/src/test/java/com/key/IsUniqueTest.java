package com.key;

import org.junit.jupiter.api.Test;

public class IsUniqueTest {
  
  IsUnique isUnique = new IsUnique();

  @Test
  public void testPalabra() {
    
    char[] s =  {'p', 'a', 'l', 'a', 'b', 'r', 'a'};
    isUnique.s = s;
    boolean result = isUnique.is_unique();
    boolean expected = false;

    assert(result == expected);
  }

  @Test
  public void testHola() {
    
    char[] s =  {'h', 'o', 'l', 'a'};
    isUnique.s = s;
    boolean result = isUnique.is_unique();
    boolean expected = true;

    assert(result == expected);
  }

  @Test
  public void testEmpty() {
    
    char[] s =  {};
    isUnique.s = s;
    boolean result = isUnique.is_unique();
    boolean expected = true;

    assert(result == expected);
  }
}
