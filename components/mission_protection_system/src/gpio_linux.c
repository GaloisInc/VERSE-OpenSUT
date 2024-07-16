// GPIO implementation for Linux, using libgpiod

#include <stdio.h>
#include <gpiod.h>
#include "common.h"
// Include `platform.h` for `ASSERT`
#include "platform.h"

#define NUM_LINES NDEV

// BEGIN code copied from libgpiod `examples/toggle_multiple_line_values.c`

static struct gpiod_line_request *
request_output_lines(const char *chip_path, const unsigned int *offsets,
                     enum gpiod_line_value *values, unsigned int num_lines,
                     const char *consumer)
{
  struct gpiod_request_config *rconfig = NULL;
  struct gpiod_line_request *request = NULL;
  struct gpiod_line_settings *settings;
  struct gpiod_line_config *lconfig;
  struct gpiod_chip *chip;
  unsigned int i;
  int ret;

  chip = gpiod_chip_open(chip_path);
  if (!chip)
    return NULL;

  settings = gpiod_line_settings_new();
  if (!settings)
    goto close_chip;

  gpiod_line_settings_set_direction(settings,
                                    GPIOD_LINE_DIRECTION_OUTPUT);

  lconfig = gpiod_line_config_new();
  if (!lconfig)
    goto free_settings;

  for (i = 0; i < num_lines; i++) {
    ret = gpiod_line_config_add_line_settings(lconfig, &offsets[i],
                                              1, settings);
    if (ret)
      goto free_line_config;
  }
  gpiod_line_config_set_output_values(lconfig, values, num_lines);

  if (consumer) {
    rconfig = gpiod_request_config_new();
    if (!rconfig)
      goto free_line_config;

    gpiod_request_config_set_consumer(rconfig, consumer);
  }

  request = gpiod_chip_request_lines(chip, rconfig, lconfig);

  gpiod_request_config_free(rconfig);

free_line_config:
  gpiod_line_config_free(lconfig);

free_settings:
  gpiod_line_settings_free(settings);

close_chip:
  gpiod_chip_close(chip);

  return request;
}

// END code copied from libgpiod `examples/toggle_multiple_line_values.c`

static int request_inited = 0;
static struct gpiod_line_request* request = NULL;

// Hardcoded device and lines for use in OpenSUT VMs.
static const char* const chip_path = "/dev/gpiochip1";
static const unsigned int line_offsets[NUM_LINES] = {0, 1};

static void init_request() {
  if (!request_inited) {
    enum gpiod_line_value values[NUM_LINES] = { GPIOD_LINE_VALUE_INACTIVE,
                                                GPIOD_LINE_VALUE_INACTIVE };
    request = request_output_lines(chip_path, line_offsets, values, NUM_LINES, "mps");
    request_inited = 1;
    if (request == NULL) {
      fprintf(stderr, "warning: failed to open GPIO device %s\n", chip_path);
    }
  }
}

void gpio_set_value(int index, int value) {
  enum gpiod_line_value gpiod_value;
  if (value == 0) {
    gpiod_value = GPIOD_LINE_VALUE_INACTIVE;
  } else {
    gpiod_value = GPIOD_LINE_VALUE_ACTIVE;
  }
  unsigned int gpiod_offset = line_offsets[index];

  init_request();
  if (request != NULL) {
    gpiod_line_request_set_value(request, gpiod_offset, gpiod_value);
  }
}
