#include "../external_deps/print.h"

/* Print out given buf, prepending msg to the output */
void buffer_print(const char *desc, const void *addr, const unsigned int len) {
  int perLine = 16;

  int i;
  unsigned char buff[perLine + 1];
  const unsigned char *pc = (const unsigned char *)addr;

  // Output description if given.

  if (desc)
    ext_printf("%s:\n", desc);

  // Length checks.

  if (len == 0) {
    ext_printf("  ZERO LENGTH\n");
    return;
  }
  if (len < 0) {
    ext_printf("  NEGATIVE LENGTH: %d\n", len);
    return;
  }

  // Process every byte in the data.

  for (i = 0; i < len; i++) {
    // Multiple of perLine means new or first line (with line offset).

    if ((i % perLine) == 0) {
      // Only print previous-line ASCII buffer for lines beyond first.

      if (i != 0)
        ext_printf("  %s\n", buff);

      // Output the offset of current line.

      ext_printf("  %04x ", i);
    }

    // Now the hex code for the specific character.

    ext_printf(" %02x", pc[i]);

    // And buffer a printable ASCII character for later.

    if ((pc[i] < 0x20) || (pc[i] > 0x7e)) // isprint() may be better.
      buff[i % perLine] = '.';
    else
      buff[i % perLine] = pc[i];
    buff[(i % perLine) + 1] = '\0';
  }

  // Pad out last line if not exactly perLine characters.

  while ((i % perLine) != 0) {
    ext_printf("   ");
    i++;
  }

  // And print the final ASCII buffer.

  ext_printf("  %s\n", buff);
}
