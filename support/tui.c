#define _GNU_SOURCE

#include <stdint.h>
#include <stdlib.h>
#include <sys/ioctl.h>

/**
 * Get the window size of stdin.
 *
 * Since the fields are unsigned short, we'll just pack them into a
 * 32-bit word for now. This avoids some FFI headaches
 */
uint32_t getWinSize () {
  struct winsize winsz;
  ioctl(0, TIOCGWINSZ, &winsz);
  return (winsz.ws_row << 16 | winsz.ws_col);
}
