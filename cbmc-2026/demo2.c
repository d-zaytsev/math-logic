#include <assert.h>

void check_pointers(char *s1, char *s2) {
  s1[0] = 42;
  s2[0] = 43;
  assert(s1[0] != s2[0]);
}

int main() {
  char c = '\0';
  check_pointers(&c, &c);
  return 0;
}
